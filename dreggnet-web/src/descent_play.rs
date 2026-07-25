//! # `descent_play` — the Lean-authored Descent, playable in a plain browser.
//!
//! `GET /descent/play` is the flagship web front door. It drives wasm
//! `NativeDescentWorld`, which is a transport wrapper around
//! `dreggnet_offerings::native_descent::NativeDescentOffering`; every click therefore crosses the
//! same executor-backed `Offering::advance` boundary as Discord, Telegram, and `/offerings/descent`.
//! The installed game program is the checked-in Lean emission. This module contains presentation
//! and persistence glue only: it does not reproduce a move rule.
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
//! directory, then the workspace `wasm/pkg`. Missing/stale wasm fails closed with a visible notice.

use std::path::{Component, Path as FsPath, PathBuf};

use axum::{
    Router,
    extract::Path as AxumPath,
    http::{StatusCode, header},
    response::{Html, IntoResponse, Response},
    routing::get,
};

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
async fn get_descent_play() -> Response {
    (
        [(header::CONTENT_SECURITY_POLICY, PLAY_CSP)],
        Html(shell_page()),
    )
        .into_response()
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
    if day.source.is_live_beacon() {
        if let Some(beacon) = crate::descent::todays_live_beacon() {
            body["round"] = serde_json::json!(beacon.round);
            body["signatureHex"] = serde_json::json!(lower_hex(&beacon.signature));
        }
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

const PLAY_STYLE: &str = r#"<style>
.nd-page{max-width:980px}.nd-intro{max-width:720px;margin:2rem 0 1.5rem}.nd-intro h1{font-size:clamp(2.6rem,9vw,6.5rem);line-height:.84;margin:.2rem 0 1rem;letter-spacing:-.045em}.nd-intro p{max-width:62ch}.nd-kicker{text-transform:uppercase;letter-spacing:.16em;font-size:.72rem;color:#c9a767}.nd-shell{border:1px solid rgba(201,167,103,.42);background:linear-gradient(145deg,rgba(17,20,32,.96),rgba(7,9,16,.98));box-shadow:0 30px 90px rgba(0,0,0,.42);padding:clamp(1rem,3vw,2rem)}.nd-meta{display:flex;flex-wrap:wrap;gap:.65rem 1.3rem;align-items:center;padding-bottom:1rem;border-bottom:1px solid rgba(255,255,255,.1);font-size:.78rem;letter-spacing:.08em;text-transform:uppercase;color:#a8aec4}.nd-proof{margin-left:auto;color:#76d3a2}.nd-grid{display:grid;grid-template-columns:repeat(4,minmax(0,1fr));gap:1px;background:rgba(255,255,255,.11);margin:1.4rem 0}.nd-stat{background:#0c101c;padding:1rem}.nd-stat b{display:block;font:600 clamp(1.2rem,4vw,2rem)/1.1 ui-monospace,SFMono-Regular,monospace;color:#f0e6cf}.nd-stat span{display:block;margin-top:.35rem;color:#8e95aa;font-size:.68rem;letter-spacing:.13em;text-transform:uppercase}.nd-custody{padding:1rem;border:1px solid rgba(255,255,255,.1);margin-bottom:1.2rem}.nd-custody strong{color:#d4ba82}.nd-action-menu{min-width:0}.nd-action-header{display:flex;gap:.6rem 1rem;align-items:baseline;justify-content:space-between;margin:1.25rem 0 .75rem}.nd-action-heading{margin:0;font-size:1rem}.nd-action-summary{margin:0;color:#8e95aa;font-size:.78rem}.nd-action-assurance{margin:0 0 .75rem;color:#777f96;font-size:.72rem;line-height:1.45}.nd-actions{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:.7rem}.nd-actions button,.nd-tools button{appearance:none;border:1px solid rgba(201,167,103,.5);background:#151a29;color:#f4eddf;padding:.85rem 1rem;text-align:left;font:inherit;cursor:pointer}.nd-actions button{min-height:48px;overflow-wrap:anywhere;touch-action:manipulation}.nd-actions button:hover:not(:disabled),.nd-tools button:hover{background:#222a3e;border-color:#d7b978}.nd-actions button:disabled{opacity:.32;cursor:not-allowed}.nd-actions button:focus-visible,.nd-tools button:focus-visible,.nd-unavailable summary:focus-visible{outline:3px solid #76d3a2;outline-offset:3px}.nd-unavailable{margin-top:.85rem;border-top:1px solid rgba(255,255,255,.08);padding-top:.7rem;color:#8e95aa}.nd-unavailable summary{cursor:pointer;font-size:.78rem;min-height:44px;display:flex;align-items:center;touch-action:manipulation}.nd-unavailable ul{list-style:none;margin:.7rem 0 0;padding:0;display:grid;gap:.35rem}.nd-unavailable li{display:flex;justify-content:space-between;gap:1rem;font-size:.75rem}.nd-unavailable-label{color:#b7bdce;overflow-wrap:anywhere}.nd-unavailable-reason{color:#666e84;text-align:right;overflow-wrap:anywhere}.nd-message{min-height:3.5rem;padding:1rem;margin:1rem 0;background:rgba(255,255,255,.045);border-left:3px solid #6b7288}.nd-message.good{border-color:#68c394}.nd-message.bad{border-color:#c76f69}.nd-tools{display:flex;flex-wrap:wrap;gap:.6rem}.nd-tools button{font-size:.78rem;padding:.6rem .8rem;min-height:44px}.nd-share{display:inline-block;margin:.2rem 0 1rem;color:#76d3a2}.nd-root{margin-top:1rem;color:#777f96;font:11px/1.5 ui-monospace,SFMono-Regular,monospace;overflow-wrap:anywhere}.nd-terminal{color:#e1bf75}.nd-fatal{padding:1rem;border:1px solid #9f514d;background:#261416;color:#f2c9c5}
/* ═══ THE VITALS — a badge and the meters that ARE the game ═══════════════ */
.nd-vitals{margin:1.4rem 0}.nd-status{display:flex;flex-wrap:wrap;gap:.55rem .9rem;align-items:center;margin-bottom:.95rem}.nd-pill{display:inline-flex;align-items:center;padding:.3rem .75rem;border-radius:999px;border:1px solid currentColor;font:700 .68rem/1 ui-monospace,SFMono-Regular,monospace;letter-spacing:.13em;text-transform:uppercase}.nd-pill.good{color:#76d3a2;background:rgba(118,211,162,.1)}.nd-pill.warn{color:#e1bf75;background:rgba(225,191,117,.1)}.nd-pill.bad{color:#e08c86;background:rgba(224,140,134,.13)}.nd-standing{color:#a8aec4;font-size:.86rem}
.nd-meters{display:grid;gap:.42rem}.nd-meter{display:grid;grid-template-columns:5.2rem 1fr 3.7rem;align-items:center;gap:.7rem}.nd-meter-label{color:#8e95aa;font:.7rem/1 ui-monospace,SFMono-Regular,monospace;letter-spacing:.11em;text-transform:uppercase}.nd-meter-track{position:relative;height:.72rem;background:rgba(255,255,255,.06);border:1px solid rgba(255,255,255,.09);overflow:hidden}.nd-meter-fill{display:block;height:100%;background:linear-gradient(90deg,#c9a767,#f0e6cf);transition:width .25s ease}.nd-meter.low .nd-meter-fill{background:linear-gradient(90deg,#8c3b36,#e08c86)}.nd-meter.done .nd-meter-fill{background:linear-gradient(90deg,#2f7a58,#76d3a2)}.nd-meter-value{color:#f0e6cf;font:.77rem/1 ui-monospace,SFMono-Regular,monospace;text-align:right}
.nd-pressure{margin:.55rem 0 0;color:#d9b48a;font-size:.8rem;line-height:1.5}
/* ═══ THE SHAFT — a relic keeps its COLUMN, so you watch it travel ════════ */
.nd-shaft{margin:1.5rem 0}.nd-shaft-heading{margin:0 0 .6rem;font-size:1rem}.nd-map{display:grid;gap:.22rem;padding:.5rem;border:1px solid rgba(255,255,255,.1);background:#080b13;max-width:34rem}.nd-cell{display:grid;place-items:center;aspect-ratio:1/1;min-width:1.1rem;border:1px solid transparent;border-radius:3px;background:rgba(255,255,255,.02);color:#5c6478;font:600 clamp(.68rem,2.3vw,1rem)/1 ui-monospace,SFMono-Regular,monospace}.nd-cell.tag-muted{color:#3f465a}.nd-cell.tag-accent{color:#f4ecd9;background:rgba(201,167,103,.15);border-color:rgba(201,167,103,.52)}.nd-cell.tag-good{color:#76d3a2}.nd-cell.tag-warn{color:#e1bf75}.nd-cell.tag-bad{color:#e08c86}.nd-cell.actionable{border-color:#76d3a2;box-shadow:0 0 12px -3px #76d3a2,inset 0 0 0 1px rgba(118,211,162,.34)}.nd-legend{margin:.5rem 0 0;color:#777f96;font:.7rem/1.75 ui-monospace,SFMono-Regular,monospace;overflow-wrap:anywhere}
@media(max-width:620px){.nd-page{padding-left:14px!important;padding-right:14px!important}.nd-intro{margin-top:1.2rem}.nd-shell{padding:13px}.nd-grid{grid-template-columns:repeat(2,minmax(0,1fr))}.nd-actions{grid-template-columns:1fr}.nd-action-header{align-items:flex-start;flex-direction:column}.nd-action-summary{line-height:1.5}.nd-unavailable li{flex-direction:column;gap:.15rem;padding:.25rem 0}.nd-unavailable-reason{text-align:left}.nd-meta{font-size:.68rem}.nd-proof{margin-left:0;width:100%}.nd-tools button{flex:1 1 auto}.nd-intro h1{font-size:3.8rem}}
/* The shaft on a phone: 11 columns of a ~360px viewport, so the cell floor is sized to keep the
   WHOLE map visible without horizontal scroll, and the meter gutters narrow to match. */
@media(max-width:620px){.nd-meter{grid-template-columns:4rem 1fr 3.1rem;gap:.5rem}.nd-map{gap:.16rem;padding:.35rem;max-width:100%}.nd-cell{min-width:0;border-radius:2px}.nd-status{gap:.4rem .6rem}.nd-legend{font-size:.64rem}}
</style>"#;

/// Static, strict-CSP chrome around the same-origin native wasm bootstrap.
fn shell_page() -> String {
    let day = crate::descent::todays_day();
    format!(
        "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\">\
         <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\
         <meta name=\"color-scheme\" content=\"dark\">\
         <title>Play The Descent — DreggNet</title>{style}{play_style}</head><body>{topbar}\
         <main class=\"session nd-page\">\
         <header class=\"nd-intro\"><p class=\"nd-kicker\">Lean-authored · locally replayed</p>\
         <h1>The Descent</h1>\
         <p>Carry relics through a finite light clock. Keys attenuate as you descend; what you do \
         not bank on a proved exit never became yours.</p></header>\
         <div id=\"descent-play-root\" data-day-key=\"{day_key}\" \
         data-native-seed=\"{native_seed}\" data-day-source=\"{day_source}\">\
         <p class=\"notice\" role=\"status\">Opening the native executor…</p>\
         </div>\
         <noscript><p class=\"notice refused\" role=\"status\">The Descent plays in-tab with \
         JavaScript + WebAssembly. The server-driven version remains available in \
         <a href=\"/offerings\">the shared offering host</a>.</p></noscript>\
         </main>{footer}\
         <script type=\"module\" src=\"/descent/play/static/app.js\"></script>\
         </body></html>",
        style = crate::STYLE,
        play_style = PLAY_STYLE,
        topbar = crate::topbar("descent"),
        day_key = crate::esc(&day.key),
        native_seed = native_seed_for_day(&day),
        day_source = if day.source.is_live_beacon() {
            "beacon"
        } else {
            "offline-date"
        },
        footer = crate::FOOTER,
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

function browserActor() {
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
    lastKind = "";
    lastMessage = "Submitting the full native record for fresh server replay…";
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
    lastKind = "good";
    const durability = result.durable === true
      ? " The artifact is in the durable Descent store."
      : " The server did not persist this artifact; keep your local replay record.";
    const anchored = result.settled === true
      ? " Anchored on the devnet node's ledger."
      : "";
    const outcome = lastShareRanked
      ? "Exact server replay passed. This crowned run now ranks in the native lane."
      : "Exact server replay passed. This settlement is shareable but did not crown, so it does not rank.";
    lastMessage = (auto ? "Run settled — auto-anchored to the board. " : "") + outcome + durability + anchored;
  } catch (e) {
    lastShare = null;
    lastKind = "bad";
    lastMessage = (auto
      ? "Auto-anchor did not complete; your local record is intact and the Publish button remains: "
      : "Publication refused; the local record remains intact: ") + errorText(e);
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
const FLOORS = 4;
const RELICS = 8;
const BREATH = 26;
const CAP = 8;
const CARRIED = 8;
const BANKED = 9;
// guard_hp(depth), indexed by depth 0..FLOORS.
const GUARD_HP = [0, 1, 1, 2, 2];

// One character per cell, so the map is the same map the Discord/Telegram/WeChat text grid paints.
const GLYPH_EMPTY = "·";
// The floor you stand on. A GLYPH, not a highlight: the highlight means "you may act on this now",
// and standing somewhere is not a move.
const GLYPH_YOU = ">";
const GLYPH_WAY_OPEN = "/";
const GLYPH_WAY_SHUT = "#";
const GLYPH_GUARDIAN = "G";
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

function relicTag(relic) {
  if (relic === 0) return "accent";
  return relic <= 3 ? "warn" : "good";
}

function countCustody(sim, code) {
  return sim.custody.filter(c => c === code).length;
}

// A labelled meter: the bar is the argument, the numbers are the proof.
function meter(label, value, max, tone) {
  const box = node("div", "nd-meter" + (tone ? " " + tone : ""));
  box.append(node("span", "nd-meter-label", label));
  const track = node("span", "nd-meter-track");
  const fill = node("span", "nd-meter-fill");
  const ratio = max > 0 ? Math.max(0, Math.min(1, value / max)) : 0;
  fill.style.width = (ratio * 100).toFixed(1) + "%";
  track.append(fill);
  box.append(track, node("span", "nd-meter-value", value + "/" + max));
  box.setAttribute("role", "img");
  box.setAttribute("aria-label", label + " " + value + " of " + max);
  return box;
}

function mapCell(glyph, tag, actionable, title) {
  const cell = node("span", "nd-cell" + (tag ? " tag-" + tag : "") + (actionable ? " actionable" : ""), glyph);
  if (title) cell.title = title;
  return cell;
}

// The shaft: four floor rows, then the pack row, then the vault row. A relic keeps its COLUMN for
// the whole run, so you watch it travel out of the dark, into your pack, and into the vault.
function buildMap(sim, actions) {
  const can = (turn, arg) => actions.some(a => a.turn === turn && a.arg === arg && a.enabled === true);
  const grid = node("div", "nd-map");
  grid.style.gridTemplateColumns = "repeat(" + MAP_COLS + ", 1fr)";
  grid.setAttribute("role", "img");
  grid.setAttribute(
    "aria-label",
    "The shaft. You stand on floor " + sim.depth + " of " + FLOORS + ". " +
    countCustody(sim, CARRIED) + " relics in your pack, " + countCustody(sim, BANKED) + " banked."
  );

  for (let floor = 1; floor <= FLOORS; floor += 1) {
    const here = sim.depth === floor;
    grid.append(mapCell(here ? GLYPH_YOU : String(floor), here ? "accent" : "muted", false,
      here ? "You stand on floor " + floor : "Floor " + floor));

    const open = floor === 1 || sim.ways[floor - 2] === 1;
    const passable = floor === sim.depth + 1 && can("delve", 0);
    const openable = floor >= 2 && can("unlock", floor);
    grid.append(mapCell(open ? GLYPH_WAY_OPEN : GLYPH_WAY_SHUT, open ? "good" : "bad",
      passable || openable,
      open ? "The way into floor " + floor + " is open" : "The way into floor " + floor + " is shut"));

    const slain = here && sim.wounds >= GUARD_HP[floor];
    grid.append(mapCell(slain ? GLYPH_GUARDIAN_SLAIN : GLYPH_GUARDIAN,
      here ? (slain ? "good" : "bad") : "muted", here && can("smite", 0),
      slain ? "The floor " + floor + " guardian has fallen" : "The floor " + floor + " guardian stands"));

    for (let relic = 0; relic < RELICS; relic += 1) {
      if (sim.custody[relic] === floor) {
        grid.append(mapCell(relicGlyph(relic), relicTag(relic), can("loot", relic),
          "Relic " + relic + " lies on floor " + floor));
      } else {
        grid.append(mapCell(GLYPH_EMPTY, "muted", false));
      }
    }
  }

  const row = (marker, markerTag, code, cellTag, what) => {
    grid.append(mapCell(marker, markerTag, false, what));
    grid.append(mapCell(GLYPH_EMPTY, "muted", false));
    grid.append(mapCell(GLYPH_EMPTY, "muted", false));
    for (let relic = 0; relic < RELICS; relic += 1) {
      if (sim.custody[relic] === code) {
        grid.append(mapCell(relicGlyph(relic), cellTag || relicTag(relic), false, what));
      } else {
        grid.append(mapCell(GLYPH_EMPTY, "muted", false));
      }
    }
  };
  row(GLYPH_PACK, "accent", CARRIED, null, "In your pack — still losable");
  row(GLYPH_VAULT, "good", BANKED, "good", "Banked — a proved exit made it yours");
  return grid;
}

// The run's one-word state. `ended` is the record's own settled bit; a run that cannot pay the one
// light every verb costs can never move again.
function standing(sim, ended) {
  if (ended) return { word: "BANKED", tone: "good" };
  if (sim.spent + 1 > BREATH) return { word: "THE LIGHT IS DEAD", tone: "bad" };
  return { word: "DELVING", tone: "warn" };
}

// The things a player is about to lose to, said out loud.
function pressures(sim, ended) {
  const lines = [];
  if (ended) return lines;
  const light = Math.max(0, BREATH - sim.spent);
  if (light <= 4) {
    lines.push("⚠ the light is guttering — " + light + " left, and climbing out costs 1");
  }
  if (sim.depth >= 1 && sim.wounds < GUARD_HP[sim.depth]) {
    const left = GUARD_HP[sim.depth] - sim.wounds;
    lines.push("⚠ the guardian stands — the hoard here stays shut until it falls (" +
      left + " more strike" + (left === 1 ? "" : "s") + ", " + left * 2 + " light)");
  }
  const pack = countCustody(sim, CARRIED);
  if (pack + 1 + sim.depth > CAP) {
    lines.push("⚠ carrying rights are spent at this depth — the next relic would not fit");
  }
  if (pack > 0) {
    lines.push("⚠ " + pack + " relic" + (pack === 1 ? "" : "s") +
      " ride" + (pack === 1 ? "s" : "") + " in the pack — nothing is yours until a proved exit banks it");
  }
  return lines;
}

function render() {
  const snapshot = JSON.parse(world.stateJson());
  const sim = snapshot.state;
  const actions = JSON.parse(world.actionsJson(actor));
  const shell = node("section", "nd-shell");
  const meta = node("div", "nd-meta");
  meta.append(
    node("span", "", "day " + (root.dataset.dayKey || "local")),
    node("span", "", "revision " + snapshot.revision),
    node("span", "", "seed " + snapshot.seed),
    node("span", "nd-proof", world.verify() ? "● replay verified" : "● verification failed")
  );
  shell.append(meta);

  // ── THE VITALS: one badge, then the meters that ARE the game. ──
  const carried = countCustody(sim, CARRIED);
  const banked = countCustody(sim, BANKED);
  const hoardHere = countCustody(sim, sim.depth);
  const state = standing(sim, snapshot.ended);
  const vitals = node("div", "nd-vitals");
  const badge = node("div", "nd-status");
  badge.append(node("span", "nd-pill " + state.tone, state.word));
  badge.append(node("span", "nd-standing", snapshot.ended
    ? "the tomb is frozen — " + banked + " relic" + (banked === 1 ? "" : "s") + " came out with you"
    : sim.depth === 0
      ? "you stand at the mouth of the shaft"
      : "floor " + sim.depth + " of " + FLOORS + " — " + hoardHere +
        " relic" + (hoardHere === 1 ? "" : "s") + " lying here"));
  if (snapshot.ended) {
    badge.append(node("span", "nd-terminal", snapshot.crowned ? "CROWNED EXIT" : "EXIT SETTLED"));
  }
  vitals.append(badge);

  const meters = node("div", "nd-meters");
  meters.append(meter("light", Math.max(0, BREATH - sim.spent), BREATH,
    BREATH - sim.spent <= 4 ? "low" : ""));
  meters.append(meter("pack", carried, Math.max(0, CAP - sim.depth),
    carried + 1 + sim.depth > CAP ? "low" : ""));
  if (sim.depth >= 1) {
    meters.append(meter("guardian", sim.wounds, GUARD_HP[sim.depth],
      sim.wounds >= GUARD_HP[sim.depth] ? "done" : ""));
  }
  meters.append(meter("banked", banked, RELICS, banked > 0 ? "done" : ""));
  vitals.append(meters);

  for (const line of pressures(sim, snapshot.ended)) {
    vitals.append(node("p", "nd-pressure", line));
  }
  shell.append(vitals);

  // ── THE MAP: the shaft itself, with what you may act on marked. ──
  const shaft = node("section", "nd-shaft");
  shaft.append(node("h2", "nd-shaft-heading", "The shaft"));
  shaft.append(buildMap(sim, actions));
  shaft.append(node("p", "nd-legend",
    "rows: floors 1–" + FLOORS + " · " + GLYPH_PACK + " your pack (still losable) · " +
    GLYPH_VAULT + " banked (yours). columns: floor · way · guardian · then one per relic " +
    "(1 crown, 2–4 way-keys, 5–8 treasures)"));
  shaft.append(node("p", "nd-legend",
    GLYPH_YOU + " you are here · " + GLYPH_WAY_OPEN + " open way · " + GLYPH_WAY_SHUT +
    " shut way · " + GLYPH_GUARDIAN + " guardian · " + GLYPH_GUARDIAN_SLAIN + " slain · " +
    GLYPH_CROWN + " crown · " + GLYPH_KEY + " way-key · " + GLYPH_TREASURE +
    " treasure · a lit cell is one you may act on now"));
  shell.append(shaft);

  const actionMenu = node("section", "nd-action-menu");
  mountDescentActionMenu(actionMenu, actions, {
    ended: snapshot.ended,
    onChoose: (action) => {
      let result;
      try { result = JSON.parse(world.advance(action.turn, action.arg, actor)); }
      catch (e) { notice("The native turn boundary failed: " + errorText(e)); return; }
      if (result.ok) {
        save();
        lastShare = null;
        lastKind = "good";
        lastMessage = "Turn committed · revision " + result.revision + " · receipt " + shortRoot(result.receiptHashHex);
      } else {
        lastKind = "bad";
        lastMessage = "Refused without advancing: " + (result.error || "the native executor declined the move");
      }
      render();
      // If that landed move settled the run, auto-anchor it to the board (once) — no manual
      // publish needed to rank.
      maybeAutoAnchor();
    },
  });
  shell.append(actionMenu);

  const message = node("p", "nd-message " + lastKind, lastMessage);
  message.setAttribute("role", "status");
  shell.append(message);

  const tools = node("div", "nd-tools");
  const verify = node("button", "", "Verify full record");
  verify.type = "button";
  verify.addEventListener("click", () => {
    const report = JSON.parse(world.verifyJson());
    lastKind = report.verified ? "good" : "bad";
    lastMessage = report.verified
      ? "Fresh replay accepted all " + report.turns + " receipts."
      : "Replay verification refused: " + report.detail;
    render();
  });
  const copy = node("button", "", "Copy replay record");
  copy.type = "button";
  copy.addEventListener("click", async () => {
    try {
      await navigator.clipboard.writeText(world.recordJson());
      lastKind = "good";
      lastMessage = "The versioned replay record is on your clipboard.";
    } catch (e) {
      lastKind = "bad";
      lastMessage = "Clipboard refused; your local run remains intact: " + errorText(e);
    }
    render();
  });
  // A terminal run auto-anchors on completion, so this button is an explicit RE-submit (the same
  // idempotent POST). It stays enabled after an auto-anchor so a player can re-publish on demand.
  const publish = node("button", "", snapshot.ended ? "Publish verified run" : "Settle before publishing");
  publish.type = "button";
  publish.disabled = !snapshot.ended || !world.verify();
  publish.addEventListener("click", () => { submitVerifiedRun(false); });
  const restart = node("button", "", "Abandon this run");
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
    lastKind = "";
    lastMessage = "Fresh run opened. No previous record was installed.";
    render();
  });
  tools.append(verify, copy, publish, restart);
  shell.append(tools);
  if (lastShare) {
    const share = node(
      "a",
      "nd-share",
      lastShareRanked ? "Open ranked native proof →" : "Open verified native record →"
    );
    share.href = lastShare;
    shell.append(share);
  }
  shell.append(node(
    "p",
    "nd-root",
    "journal root · " + snapshot.rootHex + " · actor · " + (snapshot.actor || "unclaimed")
  ));
  root.replaceChildren(shell);
}

async function boot() {
  if (!root) return;
  let wasm;
  try {
    wasm = await import("/descent/play/static/dregg_wasm.js");
    await wasm.default();
  } catch (e) {
    notice("The native WebAssembly artifact is unavailable; no substitute game was opened. " + errorText(e));
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
    if (retained) lastMessage = "Local record restored only after exact native replay.";
  } catch (e) {
    storedRemove(recordKey);
    clearAnchored();
    try { world = openFreshWorld(nativeSeed); }
    catch (openError) { notice("Native world deployment refused: " + errorText(openError)); return; }
    lastKind = "bad";
    lastMessage = "A retained record was refused and discarded: " + errorText(e);
  }
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
  throw new Error("dregg_wasm.js placeholder — the wasm bundle is not vendored (see descent_play.rs).");
}
export const __DESCENT_WASM_PLACEHOLDER = true;
"##;

#[cfg(test)]
mod tests {
    use axum::response::IntoResponse;

    #[tokio::test]
    async fn the_play_page_ships_a_strict_wasm_csp_and_mounts_the_native_root() {
        let resp = super::get_descent_play().await;
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

        let html = super::shell_page();
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
        assert!(
            html.contains("href=\"/offerings\""),
            "no-script host fallback"
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
}
