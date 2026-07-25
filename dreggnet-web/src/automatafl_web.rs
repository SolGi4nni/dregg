//! # The **automatafl table** — the bespoke web surface over the generic offering rails.
//!
//! Automatafl was already PLAYABLE at `/offerings/automatafl/session/{id}` (real commit/reveal,
//! per-viewer sealed-move fog, executor-refused illegal moves, a `TurnReceipt` per advance), but it
//! ran on the generic catalog rails with no front door: no rules page, no way to mint a table and
//! hand someone a link, no spectator view, and — the defect that actually broke the game — no
//! realtime, so in a SIMULTANEOUS-MOVE game the waiting seat had to hammer reload to learn that the
//! opponent had sealed, opened, or resolved.
//!
//! This module is the front door, modelled on the Descent's treatment in this same crate
//! (`descent.rs`: a landing/board route, a per-run route, a POST that lands a real thing):
//!
//! * `GET  /automatafl`                  — the rules + the "open a table" CTA;
//! * `POST /automatafl/table`            — MINT a table: an unguessable session id plus two
//!   unguessable per-seat links (yours + the one you send your opponent);
//! * `GET  /automatafl/table/{id}`       — a seat link. `?seat=a&key=…` is checked against the
//!   server's process key; on a match the seat label is installed as the browser's `dregg_user`
//!   cookie and the browser is redirected to the ordinary table, so the secret leaves the URL bar;
//! * `GET  /automatafl/watch/{id}`       — SPECTATE: the same board rendered for a viewer who holds
//!   no seat (both sealed moves are fog), with every control disabled;
//! * `GET  /automatafl/watch/{id}/events`— the spectator's realtime stream.
//!
//! and, mounted on the generic catalog router beside them,
//! `GET /offerings/{key}/session/{id}/events` — the per-viewer realtime stream every offering now
//! has (see [`crate::get_offering_events`]).
//!
//! ## What the seat lock actually buys (read this before believing the fog)
//!
//! The web catalog's identity is an ASSERTED label: `dregg_user` (or `?user=`) is taken at face
//! value and the actor is `blake3(label)`. On an ad-hoc session id that is a real hole for a
//! hidden-move game — *asserting the opponent's label renders the opponent's sealed move*, because
//! `render_for` discloses to whoever claims to be them.
//!
//! A table MINTED HERE closes that, and it closes it structurally rather than by obscurity:
//!
//! * the session id is `af1-` + 96 random bits, so the table is not reachable by guessing an id;
//! * each seat's label is `afs1-{a|b}-` + `blake3_keyed(K, id‖seat)` truncated to 128 bits, where
//!   `K` is a process-random key that never leaves the server. Seat A's holder cannot derive seat
//!   B's label, and a stranger cannot derive either;
//! * [`enforce_seat_lock`] REFUSES any act on an `af1-` table from a label that is not one of those
//!   two — so on a minted table the seats cannot be stolen by racing to POST first, and the
//!   sealed-move disclosure cannot be reached by asserting a label.
//!
//! **Not closed, and deliberately named:** an ad-hoc session id (`/offerings/automatafl/session/
//! my-game`) keeps the old behaviour — seats go to whoever POSTs first, and asserting the other
//! seat's label renders their sealed move. That is the whole catalog's asserted-identity model, not
//! an automatafl bug, and replacing it is a different lane. The seat lock also dies with the
//! process (K is process-random): after a restart the old links no longer verify, and the table is
//! refused rather than silently unlocked (fail-closed).

use std::convert::Infallible;
use std::sync::{Arc, OnceLock};
use std::time::Duration;

use axum::Router;
use axum::extract::{Path, Query, State};
use axum::http::{HeaderMap, StatusCode, Uri, header};
use axum::response::sse::{Event, KeepAlive, Sse};
use axum::response::{Html, IntoResponse, Response};
use axum::routing::{get, post};
use dreggnet_offerings::{Attribution, DreggIdentity, SessionId};
use serde::Deserialize;
use tokio_stream::wrappers::IntervalStream;
use tokio_stream::{Stream, StreamExt};

use crate::{CatalogState, document, esc, hex_bytes, offering_surface_fragment, web_identity};

/// The catalog key the bespoke surface plays.
pub const KEY: &str = "automatafl";

/// The prefix a SEAT-LOCKED (lobby-minted) table id wears. An id without it is an ad-hoc table on
/// the old, open seat-claiming rules — [`enforce_seat_lock`] keys off exactly this.
pub const TABLE_PREFIX: &str = "af1-";

/// The prefix a seat label wears (`afs1-a-…` / `afs1-b-…`).
const SEAT_PREFIX: &str = "afs1-";

/// How often the realtime stream re-renders the viewer's surface and pushes it if it CHANGED.
/// Server-side change detection, not a client poll: the browser holds one open `EventSource` and
/// never reloads. 400 ms is well under human reaction time on a turn-based board and costs one
/// in-process render per connected viewer per tick.
const PULSE: Duration = Duration::from_millis(400);

/// The SSE keep-alive comment interval (holds the connection open through idle proxies).
const KEEPALIVE: Duration = Duration::from_secs(15);

// ─────────────────────────────────────────────────────────────────────────────────────────
// THE SEAT LOCK
// ─────────────────────────────────────────────────────────────────────────────────────────

/// The process-random key the per-seat labels are derived under. Never served, never persisted:
/// a restart invalidates every outstanding seat link (the table is then REFUSED, not unlocked).
fn seat_key() -> &'static [u8; 32] {
    static KEY_CELL: OnceLock<[u8; 32]> = OnceLock::new();
    KEY_CELL.get_or_init(|| {
        let mut key = [0_u8; 32];
        getrandom::fill(&mut key).expect("operating-system RNG must mint the automatafl seat key");
        key
    })
}

/// A seat of the two-player table, as it appears in a link (`a` / `b`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SeatSlot {
    /// The link the table's opener keeps (`?seat=a`).
    A,
    /// The link the opener sends (`?seat=b`) — the invite.
    B,
}

impl SeatSlot {
    /// The lowercase letter the link and the label carry.
    pub fn letter(self) -> char {
        match self {
            SeatSlot::A => 'a',
            SeatSlot::B => 'b',
        }
    }

    /// The seat a link's `?seat=` names (case-insensitive), if it names one.
    pub fn parse(raw: &str) -> Option<SeatSlot> {
        match raw.trim().to_ascii_lowercase().as_str() {
            "a" => Some(SeatSlot::A),
            "b" => Some(SeatSlot::B),
            _ => None,
        }
    }
}

/// **Mint a seat-locked table id** — `af1-` plus 96 bits of OS randomness. Not derived from
/// anything a caller supplies, so a table is not reachable by guessing.
pub fn mint_table_id() -> String {
    let mut bytes = [0_u8; 12];
    getrandom::fill(&mut bytes).expect("operating-system RNG must mint the automatafl table id");
    format!("{TABLE_PREFIX}{}", hex_bytes(&bytes))
}

/// **The seat's secret label** — `afs1-{a|b}-` + 128 bits of `blake3_keyed(K, id‖seat)`. This IS
/// the browser identity for that seat (the catalog derives the actor as `blake3(label)`), so
/// holding the label is holding the seat, and the label is not derivable without `K`.
pub fn seat_label(id: &str, seat: SeatSlot) -> String {
    let mut input = Vec::with_capacity(id.len() + 1);
    input.extend_from_slice(id.as_bytes());
    input.push(seat.letter() as u8);
    let tag = blake3::keyed_hash(seat_key(), &input);
    format!(
        "{SEAT_PREFIX}{}-{}",
        seat.letter(),
        hex_bytes(&tag.as_bytes()[..16])
    )
}

/// The seat `label` holds at table `id`, if any. Constant-shape: both seats are always derived and
/// compared, so a mismatch does not leak which seat was closer.
pub fn seat_of_label(id: &str, label: &str) -> Option<SeatSlot> {
    let a = seat_label(id, SeatSlot::A);
    let b = seat_label(id, SeatSlot::B);
    let is_a = constant_time_eq(a.as_bytes(), label.as_bytes());
    let is_b = constant_time_eq(b.as_bytes(), label.as_bytes());
    match (is_a, is_b) {
        (true, _) => Some(SeatSlot::A),
        (_, true) => Some(SeatSlot::B),
        _ => None,
    }
}

fn constant_time_eq(left: &[u8], right: &[u8]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut diff = 0_u8;
    for (l, r) in left.iter().zip(right.iter()) {
        diff |= l ^ r;
    }
    diff == 0
}

/// Whether `id` names a SEAT-LOCKED table (one minted by [`mint_table_id`]).
pub fn is_locked_table(id: &str) -> bool {
    id.starts_with(TABLE_PREFIX)
}

/// **The gate the generic act routes call.** On a seat-locked automatafl table, only the two minted
/// seat labels may act — so a stranger who learns the id cannot race in and claim a seat, and an
/// asserted `?user=` cannot reach the sealed-move disclosure. `Ok(())` on every other route/key,
/// byte-identically to before this module existed.
///
/// Returns the refusal text to render when the actor is not seated.
pub fn enforce_seat_lock(key: &str, id: &str, actor_label: &str) -> Result<(), String> {
    if key != KEY || !is_locked_table(id) {
        return Ok(());
    }
    if seat_of_label(id, actor_label).is_some() {
        return Ok(());
    }
    Err(
        "this is a seat-locked table — open your seat link to sit down (nothing committed)"
            .to_string(),
    )
}

// ─────────────────────────────────────────────────────────────────────────────────────────
// THE ROUTER
// ─────────────────────────────────────────────────────────────────────────────────────────

/// **Assemble the automatafl front door.** Merged into the demo app by `make_app`; additive — it
/// adds no route that overlaps the catalog's `/offerings/**` surface.
pub fn automatafl_router(state: Arc<CatalogState>) -> Router {
    Router::new()
        .route("/automatafl", get(get_landing))
        .route("/automatafl/", get(get_landing))
        .route("/automatafl/table", post(post_new_table))
        .route("/automatafl/table/{id}", get(get_seat_link))
        .route("/automatafl/watch/{id}", get(get_spectate))
        .route("/automatafl/watch/{id}/events", get(get_spectate_events))
        .with_state(state)
}

/// `GET /automatafl` — the front door: what the game IS, how a turn resolves, and the one control
/// that matters (open a table).
async fn get_landing() -> Html<String> {
    Html(landing_page(None))
}

/// `POST /automatafl/table` — mint a seat-locked table and hand back both links.
async fn post_new_table(State(state): State<Arc<CatalogState>>) -> Response {
    let id = mint_table_id();
    let sid = SessionId::new(id.clone());
    // Deploy the world now, attributed to seat A's label, so the invite link opens a table that
    // already exists (and a refusal is surfaced HERE rather than on the guest's first click).
    let opener = web_identity(&seat_label(&id, SeatSlot::A));
    if let Err(error) = state.ensure_open_and_bind(
        KEY,
        &sid,
        &opener,
        Some(Attribution::Asserted {
            label: opener.0.clone(),
        }),
    ) {
        return (
            StatusCode::CONFLICT,
            Html(landing_page(Some(&format!(
                "Refused: the table could not be opened — {error}"
            )))),
        )
            .into_response();
    }
    Html(lobby_page(&id)).into_response()
}

/// The `?seat=&key=` of a seat link.
#[derive(Debug, Clone, Default, Deserialize)]
pub struct SeatQuery {
    #[serde(default)]
    pub seat: Option<String>,
    #[serde(default)]
    pub key: Option<String>,
}

/// `GET /automatafl/table/{id}?seat=a&key=…` — take the seat.
///
/// The `key` is checked against the process-derived label for that seat. On a match the label is
/// installed as the browser's `HttpOnly` `dregg_user` cookie and the browser is sent (303) to the
/// ordinary table URL, so the secret leaves the address bar (and the referrer) immediately.
async fn get_seat_link(
    Path(id): Path<String>,
    Query(query): Query<SeatQuery>,
    uri: Uri,
    request_headers: HeaderMap,
) -> Response {
    let seat = query.seat.as_deref().and_then(SeatSlot::parse);
    let key = query.key.as_deref().unwrap_or_default();
    let expected = seat.map(|s| seat_label(&id, s));
    let ok = match (&expected, seat) {
        (Some(expected), Some(_)) => constant_time_eq(expected.as_bytes(), key.as_bytes()),
        _ => false,
    };
    if !ok {
        return (StatusCode::FORBIDDEN, Html(seat_refused_page(&id))).into_response();
    }
    let label = expected.expect("a verified seat link names a seat");
    let mut response = (StatusCode::SEE_OTHER, Html(seat_taken_page(&id))).into_response();
    let headers = response.headers_mut();
    headers.insert(
        header::LOCATION,
        format!("/offerings/{KEY}/session/{id}")
            .parse()
            .expect("the table location is header-safe"),
    );
    // `Secure` on exactly the same evidence the visitor-cookie bootstrap uses
    // ([`crate::web_identity_http::bootstrap_visitor_identity`]): the request's own scheme, or the
    // `X-Forwarded-Proto` the TLS-terminating edge sets. The seat label IS the seat — a browser
    // must never be willing to put it on a plaintext hop when the session it came from was https.
    let secure = uri.scheme_str() == Some("https")
        || request_headers
            .get("x-forwarded-proto")
            .and_then(|value| value.to_str().ok())
            .is_some_and(|proto| proto.eq_ignore_ascii_case("https"));
    let secure_attribute = if secure { "; Secure" } else { "" };
    headers.insert(
        header::SET_COOKIE,
        format!(
            "dregg_user={label}; Path=/; Max-Age=86400; HttpOnly; SameSite=Lax{secure_attribute}"
        )
        .parse()
        .expect("the seat cookie is header-safe"),
    );
    // The seat secret is in THIS url. Never hand it to the next hop.
    headers.insert(
        header::REFERRER_POLICY,
        "no-referrer".parse().expect("static header value"),
    );
    headers.insert(
        header::CACHE_CONTROL,
        "private, no-store".parse().expect("static header value"),
    );
    response
}

/// A fresh, unguessable SPECTATOR identity. Never equal to a seat label and never equal to a
/// canonical seat identity, so `AutomataflSession::seat_of` answers `None` and BOTH sealed moves
/// stay fogged — the spectator view is the fog path the offering already implements, finally given
/// a route.
fn spectator_identity() -> DreggIdentity {
    let mut bytes = [0_u8; 16];
    getrandom::fill(&mut bytes).expect("operating-system RNG must mint a spectator label");
    web_identity(&format!("af-spectator-{}", hex_bytes(&bytes)))
}

/// `GET /automatafl/watch/{id}` — the spectator table: the live board, both moves fogged, every
/// control disabled.
async fn get_spectate(State(state): State<Arc<CatalogState>>, Path(id): Path<String>) -> Response {
    let sid = SessionId::new(id.clone());
    let viewer = spectator_identity();
    // WATCHING NEVER OPENS A TABLE. The ordinary session route deploys a world on first touch, which
    // is right for a player and wrong for a spectator: it would let anyone mint an unplayable table
    // by typing a URL. So the render is attempted directly — a table that does not exist answers
    // "no such table" instead of quietly becoming one.
    let Some(fragment) = offering_surface_fragment(&state, KEY, &sid, None, &viewer) else {
        return (StatusCode::NOT_FOUND, Html(watch_missing_page(&id))).into_response();
    };
    Html(spectate_page(&id, &fragment)).into_response()
}

/// `GET /automatafl/watch/{id}/events` — the spectator's realtime stream (fogged, like the page).
async fn get_spectate_events(
    State(state): State<Arc<CatalogState>>,
    Path(id): Path<String>,
) -> Response {
    let sid = SessionId::new(id);
    let viewer = spectator_identity();
    surface_stream(state, KEY.to_string(), sid, viewer).into_response()
}

// ─────────────────────────────────────────────────────────────────────────────────────────
// THE REALTIME STREAM — shared by the spectator route and the generic per-offering route.
// ─────────────────────────────────────────────────────────────────────────────────────────

/// **The realtime surface stream.** One open `EventSource` per viewer; the server re-renders THAT
/// VIEWER's fragment every [`PULSE`] and pushes it only when the rendered bytes CHANGED. So the
/// waiting seat in a simultaneous-move game learns that the opponent sealed / opened / resolved
/// without touching reload — and, because each frame is the viewer's OWN per-viewer render, the fog
/// is exactly the fog the page was served with (a spectator's stream never carries a sealed move).
///
/// Change detection is server-side, so an idle table costs one cheap in-process render per tick and
/// pushes nothing. Degradation is total and silent: a client with no `EventSource` (or with JS off)
/// simply never opens the stream and keeps the server-form reload path, unchanged.
///
/// HONEST COST, unmitigated here: each tick is a render on the offering HOST THREAD — the same
/// single-threaded boundary the act path uses. A handful of viewers is nothing (a few renders a
/// second), but there is no cap on concurrent subscriptions, so a public deployment wanting to be
/// robust against a subscription flood needs a per-IP stream limit in front of this. Naming it
/// rather than pretending the polling is free.
pub(crate) fn surface_stream(
    state: Arc<CatalogState>,
    key: String,
    id: SessionId,
    viewer: DreggIdentity,
) -> Sse<impl Stream<Item = Result<Event, Infallible>>> {
    let mut ticks = tokio::time::interval(PULSE);
    // A slow render must never leave a BURST of catch-up ticks queued behind it — that would turn a
    // momentarily busy host into a render storm. Skipped ticks are simply lost; the next render is a
    // complete snapshot, so nothing is missed.
    ticks.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Delay);
    let mut last: Option<[u8; 32]> = None;
    let stream = IntervalStream::new(ticks).filter_map(move |_| {
        let fragment = offering_surface_fragment(&state, &key, &id, None, &viewer)?;
        let digest = *blake3::hash(fragment.as_bytes()).as_bytes();
        if last == Some(digest) {
            return None;
        }
        last = Some(digest);
        Some(Ok::<Event, Infallible>(
            Event::default().data(one_line(&fragment)),
        ))
    });
    Sse::new(stream).keep_alive(KeepAlive::new().interval(KEEPALIVE).text("keep-alive"))
}

/// Flatten a fragment onto ONE `data:` line. SSE rejoins multi-line payloads with `\n`, which would
/// survive into the swapped HTML; HTML is whitespace-insensitive here, so collapsing is lossless
/// for the render and keeps the frame a single line for a reader tailing the stream.
fn one_line(html: &str) -> String {
    html.replace(['\r', '\n'], " ")
}

// ─────────────────────────────────────────────────────────────────────────────────────────
// THE PAGES
// ─────────────────────────────────────────────────────────────────────────────────────────

/// The rules block — what a stranger needs to know before their first click, and no more.
fn rules_html() -> String {
    let n = dregg_automatafl::game::N;
    format!(
        "<section class=\"panel\"><h2>The rules, in one screen</h2>\
         <ul class=\"rules\">\
         <li><strong>The board</strong> is {n}×{n}. It holds <code>R</code> repulsors, \
         <code>A</code> attractors, and ONE <code>@</code> automaton. Pieces move like a rook \
         (any distance along a row or a column, never diagonally, never onto the automaton).</li>\
         <li><strong>You do not take turns.</strong> Both seats seal a move at the same time. The \
         round runs <em>commit → reveal → resolve</em>: you seal, your opponent seals, both open, \
         then ONE turn applies both.</li>\
         <li><strong>The seal is the game.</strong> While a move is sealed the opponent sees only \
         its commitment — no source, no destination. That fog is the mechanic, so the table is \
         rendered per viewer: your own move is in the clear to you and to nobody else.</li>\
         <li><strong>Conflicts drop.</strong> If the two moves fight over a square, the resolution \
         drops them and the round still ends. (The published ruleset instead marks the square and \
         re-enters the round; this surface does not, and a match containing such a round is \
         refused by the match fold rather than attested.)</li>\
         <li><strong>The automaton then steps</strong>, pulled toward attractors and pushed from \
         repulsors along each axis. Drive it onto one of YOUR two goal corners and you win.</li>\
         </ul>\
         <p class=\"prose\">Every press is one real executor turn: an illegal move is REFUSED with \
         nothing committed, and a landed one returns a <code>TurnReceipt</code>. The whole match \
         re-verifies by in-process replay — no node, no testnet.</p>\
         </section>",
        n = n,
    )
}

/// `GET /automatafl` — the landing page.
fn landing_page(notice: Option<&str>) -> String {
    let body = format!(
        "<main class=\"session\">\
         <div class=\"page-head\" style=\"padding-top:var(--s4)\">\
         <h1>Automatafl</h1>\
         <p class=\"deck\">A simultaneous-move board game where the piece that wins it is the one \
         neither player controls.</p></div>\
         {notice}\
         <section class=\"panel\"><h2>Open a table</h2>\
         <p class=\"prose\">A table is minted with two seat links. Keep one, send the other — \
         whoever opens a link takes that seat, and nobody else can.</p>\
         <form method=\"post\" action=\"/automatafl/table\" class=\"affordance\">\
         <button type=\"submit\">Open a table</button></form>\
         </section>\
         {rules}\
         <p class=\"prose\"><a class=\"backlink\" href=\"/offerings\">← the Lab</a></p>\
         </main>",
        notice = notice
            .map(|n| format!(
                "<div class=\"notice refused\" role=\"status\">{}</div>",
                esc(n)
            ))
            .unwrap_or_default(),
        rules = rules_html(),
    );
    document("DreggNet Cloud — Automatafl", "offerings", &body)
}

/// The lobby page a mint returns — the two seat links plus the spectator link.
fn lobby_page(id: &str) -> String {
    let a = seat_link(id, SeatSlot::A);
    let b = seat_link(id, SeatSlot::B);
    let body = format!(
        "<main class=\"session\">\
         <div class=\"page-head\" style=\"padding-top:var(--s4)\">\
         <h1>Table opened</h1>\
         <p class=\"deck\">Session <span class=\"sid\">{id}</span> — seat-locked. Only these two \
         links can sit down.</p></div>\
         <section class=\"panel\"><h2>Your link</h2>\
         <p class=\"prose\">Open this one yourself. (Which side of the board you get — seat A or \
         seat B — is settled by the game when you make your first move; the link decides only that \
         the table is <em>yours</em>.)</p>\
         <p><a class=\"seat-link\" href=\"{a}\">Sit down →</a></p>\
         <p class=\"invite\"><code>{a}</code></p>\
         </section>\
         <section class=\"panel\"><h2>The invite</h2>\
         <p class=\"prose\">Send this to your opponent. It <em>is</em> the seat — anyone holding it \
         can sit down and nobody else can, so send it the way you would send a key.</p>\
         <p class=\"invite\"><code>{b}</code></p>\
         <p><a class=\"seat-link\" href=\"{b}\">(or take this side yourself)</a></p>\
         </section>\
         <section class=\"panel\"><h2>Anyone else</h2>\
         <p class=\"prose\">Spectators see the live board with BOTH sealed moves fogged and every \
         control disabled.</p>\
         <p class=\"invite\"><code>/automatafl/watch/{id}</code></p>\
         <p><a class=\"seat-link\" href=\"/automatafl/watch/{id}\">Watch this table →</a></p>\
         </section>\
         <p class=\"prose\"><a class=\"backlink\" href=\"/automatafl\">← the rules</a></p>\
         </main>",
        id = esc(id),
        a = esc(&a),
        b = esc(&b),
    );
    document("DreggNet Cloud — table opened", "offerings", &body)
}

/// The seat link for `seat` at `id` (relative — the deployment's own origin).
pub fn seat_link(id: &str, seat: SeatSlot) -> String {
    format!(
        "/automatafl/table/{id}?seat={letter}&key={label}",
        id = id,
        letter = seat.letter(),
        label = seat_label(id, seat),
    )
}

/// The page a bad/absent seat key gets — honest, and it points at the thing they CAN do.
fn seat_refused_page(id: &str) -> String {
    let body = format!(
        "<main class=\"session\">\
         <div class=\"notice refused\" role=\"status\">That seat link is not valid for this table. \
         Seat links are minted per table and do not survive a server restart.</div>\
         <p class=\"prose\">You can still watch: \
         <a class=\"backlink\" href=\"/automatafl/watch/{id}\">spectate this table →</a></p>\
         <p class=\"prose\"><a class=\"backlink\" href=\"/automatafl\">← open your own table</a></p>\
         </main>",
        id = esc(id),
    );
    document("DreggNet Cloud — seat refused", "offerings", &body)
}

/// The 303 body (a browser follows the `Location`; this is what a non-following client reads).
fn seat_taken_page(id: &str) -> String {
    let body = format!(
        "<main class=\"session\"><div class=\"notice ok\" role=\"status\">Seat taken — \
         opening the table.</div>\
         <p class=\"prose\"><a class=\"backlink\" href=\"/offerings/{KEY}/session/{id}\">\
         Go to the table →</a></p></main>",
        id = esc(id),
    );
    document("DreggNet Cloud — seat taken", "offerings", &body)
}

fn watch_missing_page(id: &str) -> String {
    let body = format!(
        "<main class=\"session\"><div class=\"notice refused\" role=\"status\">No automatafl table \
         at <code>{id}</code>. Watching does not open one — a table exists once somebody mints it.\
         </div>\
         <p class=\"prose\"><a class=\"backlink\" href=\"/automatafl\">← open a table</a></p>\
         </main>",
        id = esc(id),
    );
    document("DreggNet Cloud — no such table", "offerings", &body)
}

/// The spectator page. The live region carries `data-readonly`, and the served surface is wrapped
/// in a `disabled` `<fieldset>` — the HTML-native way to make every descendant control inert, so
/// the read-only rendering needs no parsing of the offering's own markup and cannot drift from it.
///
/// A spectator who re-enables the controls by hand gains nothing they did not already have: their
/// POST would land under the spectator identity, exactly as any anonymous visitor's already can on
/// an ad-hoc table — and on a seat-locked table [`enforce_seat_lock`] refuses it outright.
fn spectate_page(id: &str, fragment: &str) -> String {
    let body = format!(
        "<div class=\"crumb\"><a href=\"/automatafl\">← Automatafl</a>\
         <span class=\"sep\">·</span><strong>spectating</strong>\
         <span class=\"sep\">·</span><span class=\"sid\">session {id}</span></div>\
         <main class=\"session\">\
         <div class=\"page-head\" style=\"padding-top:var(--s4)\"><h1>Spectating</h1>\
         <p class=\"deck\">Both sealed moves are fog to you — you see a commitment, never a \
         destination, until the seats open them.</p></div>\
         <div id=\"live-surface\" class=\"live-surface spectating\" tabindex=\"-1\" \
         aria-live=\"polite\" data-readonly=\"1\" \
         data-events=\"/automatafl/watch/{id}/events\">\
         <fieldset class=\"spectate-lock\" disabled>{fragment}</fieldset></div>\
         </main>",
        id = esc(id),
        fragment = fragment,
    );
    document(
        &format!("DreggNet Cloud — spectating {id}"),
        "offerings",
        &body,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_seat_label_is_not_derivable_from_the_other_seat() {
        let id = mint_table_id();
        let a = seat_label(&id, SeatSlot::A);
        let b = seat_label(&id, SeatSlot::B);
        assert_ne!(a, b, "the two seats carry different labels");
        assert_eq!(seat_of_label(&id, &a), Some(SeatSlot::A));
        assert_eq!(seat_of_label(&id, &b), Some(SeatSlot::B));
        // A label minted for ANOTHER table does not open this one.
        let other = mint_table_id();
        assert_eq!(seat_of_label(&id, &seat_label(&other, SeatSlot::A)), None);
        // And an asserted plain label opens nothing.
        assert_eq!(seat_of_label(&id, "alice"), None);
    }

    #[test]
    fn the_seat_lock_only_binds_minted_tables() {
        let id = mint_table_id();
        assert!(enforce_seat_lock(KEY, &id, "alice").is_err());
        assert!(enforce_seat_lock(KEY, &id, &seat_label(&id, SeatSlot::B)).is_ok());
        // An ad-hoc id keeps the old open behaviour; another key is untouched entirely.
        assert!(enforce_seat_lock(KEY, "auto-1", "alice").is_ok());
        assert!(enforce_seat_lock("tug", &id, "alice").is_ok());
    }

    #[test]
    fn a_seat_slot_round_trips_through_a_link() {
        let id = mint_table_id();
        let link = seat_link(&id, SeatSlot::B);
        assert!(link.starts_with(&format!(
            "/automatafl/table/{id}?seat=b&key={SEAT_PREFIX}b-"
        )));
        assert_eq!(SeatSlot::parse("B"), Some(SeatSlot::B));
        assert_eq!(SeatSlot::parse("c"), None);
    }
}
