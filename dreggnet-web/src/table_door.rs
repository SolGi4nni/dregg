//! # The **front door**, shared by every seat-locked two-player table.
//!
//! Automatafl had the only good joining experience in the portfolio: mint a table, get two secret
//! seat links, keep one, send the other, and watch from a third. The tug had none — every visitor
//! landed on ONE publicly-advertised table and the first two identities to press a button took the
//! seats, which is a race condition wearing a lobby's clothes.
//!
//! Rather than write that experience a second time (and grow a second, subtly different seat
//! authorisation), the whole door is here, parameterised by a [`TableLock`]:
//!
//! * `GET  {route}`                  — the game's rules + the "open a table" CTA (the ONE part each
//!   game supplies itself, via [`TableDoor::landing`]);
//! * `POST {route}/table`            — MINT: an unguessable session id plus two unguessable per-seat
//!   links, with the world deployed so the invite opens a table that already exists;
//! * `GET  {route}/table/{id}`       — a seat link. `?seat=a&key=…` is checked against the server's
//!   key; on a match the seat label becomes the browser's `HttpOnly dregg_user` cookie and the
//!   browser is redirected to the ordinary table, so the secret leaves the URL bar;
//! * `POST {route}/table/{id}/resign`— end your own table. The only resolution a player can cause,
//!   and it can only ever cost the person who fires it;
//! * `GET  {route}/watch/{id}`       — SPECTATE: the same board rendered for a viewer holding no
//!   seat (every private projection is fog), with every control inert;
//! * `GET  {route}/watch/{id}/events`— the spectator's realtime stream.
//!
//! Every one of those routes [`crate::table_seats::touch`]es the table first, so a stalled match is
//! resolved as of the visitor's own click rather than sitting in a phase forever.

use std::convert::Infallible;
use std::sync::Arc;
use std::time::{Duration, Instant};

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

use crate::table_seats::{self, Resolution, SeatSlot, TableLock};
use crate::web_identity_http::web_user_established;
use crate::{
    CatalogState, WebQuery, document, esc, hex_bytes, offering_surface_fragment, web_identity,
};

/// How often the realtime stream re-renders the viewer's surface and pushes it if it CHANGED.
/// Server-side change detection, not a client poll: the browser holds one open `EventSource` and
/// never reloads. 400 ms is well under human reaction time on a turn-based board and costs one
/// in-process render per connected viewer per tick.
const PULSE: Duration = Duration::from_millis(400);

/// The SSE keep-alive comment interval (holds the connection open through idle proxies).
const KEEPALIVE: Duration = Duration::from_secs(15);

/// **One game's front door.** The lock supplies every route path and the seat derivation; the two
/// function pointers and two prose lines are the whole per-game surface area.
#[derive(Clone)]
pub struct TableDoor {
    /// The seat lock (and therefore the catalog key, the id/label prefixes, and the route base).
    pub lock: TableLock,
    /// The catalog host.
    pub catalog: Arc<CatalogState>,
    /// The game's own landing page (rules + the mint CTA), given an optional notice to surface.
    pub landing: fn(Option<&str>) -> String,
    /// What the two seat links mean at this table, in one sentence for the lobby.
    pub seat_note: &'static str,
    /// What a spectator can and cannot see here, in one sentence.
    pub spectator_note: &'static str,
}

/// **Assemble a game's front door.** Additive — every path is under the game's own `route`, so it
/// never overlaps the catalog's `/offerings/**` surface.
pub fn table_router(door: TableDoor) -> Router {
    let route = door.lock.route;
    Router::new()
        .route(route, get(get_landing))
        .route(&format!("{route}/"), get(get_landing))
        .route(&format!("{route}/table"), post(post_new_table))
        .route(&format!("{route}/table/{{id}}"), get(get_seat_link))
        .route(&format!("{route}/table/{{id}}/resign"), post(post_resign))
        .route(&format!("{route}/watch/{{id}}"), get(get_spectate))
        .route(
            &format!("{route}/watch/{{id}}/events"),
            get(get_spectate_events),
        )
        .with_state(door)
}

// ─────────────────────────────────────────────────────────────────────────────────────────
// MINT
// ─────────────────────────────────────────────────────────────────────────────────────────

/// `GET {route}` — the game's own front page.
async fn get_landing(State(door): State<TableDoor>) -> Html<String> {
    Html((door.landing)(None))
}

/// `POST {route}/table` — mint a seat-locked table and hand back both links.
async fn post_new_table(State(door): State<TableDoor>) -> Response {
    let id = door.lock.mint_table_id();
    let sid = SessionId::new(id.clone());
    // Deploy the world NOW, attributed to seat A's label, so the invite link opens a table that
    // already exists (and a refusal is surfaced HERE rather than on the guest's first click).
    let opener = web_identity(&door.lock.seat_label(&id, SeatSlot::A));
    if let Err(error) = door.catalog.ensure_open_and_bind(
        door.lock.key,
        &sid,
        &opener,
        Some(Attribution::Asserted {
            label: opener.0.clone(),
        }),
    ) {
        return (
            StatusCode::CONFLICT,
            Html((door.landing)(Some(&format!(
                "Refused: the table could not be opened — {error}"
            )))),
        )
            .into_response();
    }
    table_seats::registry().opened(door.lock, &id, Instant::now());
    Html(lobby_page(&door, &id)).into_response()
}

// ─────────────────────────────────────────────────────────────────────────────────────────
// SIT DOWN
// ─────────────────────────────────────────────────────────────────────────────────────────

/// The `?seat=&key=` of a seat link.
#[derive(Debug, Clone, Default, Deserialize)]
pub struct SeatQuery {
    /// Which seat the link claims (`a` / `b`).
    #[serde(default)]
    pub seat: Option<String>,
    /// The seat secret.
    #[serde(default)]
    pub key: Option<String>,
}

/// `GET {route}/table/{id}?seat=a&key=…` — take the seat.
///
/// The `key` is checked against the server-derived label for that seat. On a match the label is
/// installed as the browser's `HttpOnly` `dregg_user` cookie and the browser is sent (303) to the
/// ordinary table URL, so the secret leaves the address bar (and the referrer) immediately.
async fn get_seat_link(
    State(door): State<TableDoor>,
    Path(id): Path<String>,
    Query(query): Query<SeatQuery>,
    uri: Uri,
    request_headers: HeaderMap,
) -> Response {
    // A seat link is the commonest way somebody looks at a stalled table: resolve it first, so the
    // returning player is told the match ended rather than handed a dead board.
    if let Some(resolution) = table_seats::touch(&door.catalog, &id) {
        return (
            StatusCode::GONE,
            Html(resolved_page(&door, &id, &resolution)),
        )
            .into_response();
    }
    let seat = query.seat.as_deref().and_then(SeatSlot::parse);
    let key = query.key.as_deref().unwrap_or_default();
    let expected = seat.map(|s| door.lock.seat_label(&id, s));
    let ok = match (&expected, seat) {
        (Some(expected), Some(_)) => constant_time_eq(expected.as_bytes(), key.as_bytes()),
        _ => false,
    };
    if !ok {
        return (StatusCode::FORBIDDEN, Html(seat_refused_page(&door, &id))).into_response();
    }
    let label = expected.expect("a verified seat link names a seat");
    let mut response = (StatusCode::SEE_OTHER, Html(seat_taken_page(&door, &id))).into_response();
    let headers = response.headers_mut();
    headers.insert(
        header::LOCATION,
        door.lock
            .table_link(&id)
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

// ─────────────────────────────────────────────────────────────────────────────────────────
// RESIGN
// ─────────────────────────────────────────────────────────────────────────────────────────

/// `POST {route}/table/{id}/resign` — end your own table.
///
/// The actor is the seat label already in the browser's `dregg_user` cookie (the seat link put it
/// there), so this needs no secret in the body and cannot be aimed at anyone else: it resolves the
/// table against **whichever seat fired it**. A visitor holding neither seat is refused.
async fn post_resign(
    State(door): State<TableDoor>,
    Path(id): Path<String>,
    headers: HeaderMap,
    Query(query): Query<WebQuery>,
) -> Response {
    let (label, _) = web_user_established(&headers, &query);
    let Some(seat) = door.lock.seat_of_label(&id, &label) else {
        return (StatusCode::FORBIDDEN, Html(seat_refused_page(&door, &id))).into_response();
    };
    let Some(resolution) = table_seats::resign(&id, seat) else {
        // The table is not in this process's registry — a link from before a restart. Fail-closed:
        // there is nothing here to resign.
        return (StatusCode::NOT_FOUND, Html(watch_missing_page(&door, &id))).into_response();
    };
    (StatusCode::OK, Html(resolved_page(&door, &id, &resolution))).into_response()
}

// ─────────────────────────────────────────────────────────────────────────────────────────
// SPECTATE
// ─────────────────────────────────────────────────────────────────────────────────────────

/// A fresh, unguessable SPECTATOR identity. Never equal to a seat label and never equal to a
/// canonical seat identity, so the offering's own `seat_of` answers `None` and every private
/// projection stays fogged — the spectator view is the fog path each offering already implements,
/// finally given a route.
fn spectator_identity(lock: &TableLock) -> DreggIdentity {
    let mut bytes = [0_u8; 16];
    getrandom::fill(&mut bytes).expect("operating-system RNG must mint a spectator label");
    web_identity(&format!(
        "{}spectator-{}",
        lock.seat_prefix,
        hex_bytes(&bytes)
    ))
}

/// `GET {route}/watch/{id}` — the spectator table: the live board, every hidden projection fogged,
/// every control inert.
async fn get_spectate(State(door): State<TableDoor>, Path(id): Path<String>) -> Response {
    let resolution = table_seats::touch(&door.catalog, &id);
    let sid = SessionId::new(id.clone());
    let viewer = spectator_identity(&door.lock);
    // WATCHING NEVER OPENS A TABLE. The ordinary session route deploys a world on first touch,
    // which is right for a player and wrong for a spectator: it would let anyone mint an unplayable
    // table by typing a URL. So the render is attempted directly — a table that does not exist
    // answers "no such table" instead of quietly becoming one.
    let Some(fragment) =
        offering_surface_fragment(&door.catalog, door.lock.key, &sid, None, &viewer)
    else {
        return (StatusCode::NOT_FOUND, Html(watch_missing_page(&door, &id))).into_response();
    };
    Html(spectate_page(&door, &id, &fragment, resolution.as_ref())).into_response()
}

/// `GET {route}/watch/{id}/events` — the spectator's realtime stream (fogged, like the page).
async fn get_spectate_events(State(door): State<TableDoor>, Path(id): Path<String>) -> Response {
    // The stream is the ONE surface a waiting player leaves open, so it is also the cheapest place
    // to notice that the table died: reap on subscription, then let the change-detection push the
    // resolved render.
    table_seats::touch(&door.catalog, &id);
    let sid = SessionId::new(id);
    let viewer = spectator_identity(&door.lock);
    surface_stream(
        Arc::clone(&door.catalog),
        door.lock.key.to_string(),
        sid,
        viewer,
    )
    .into_response()
}

// ─────────────────────────────────────────────────────────────────────────────────────────
// THE REALTIME STREAM — shared by the spectator routes and the generic per-offering route.
// ─────────────────────────────────────────────────────────────────────────────────────────

/// **The realtime surface stream.** One open `EventSource` per viewer; the server re-renders THAT
/// VIEWER's fragment every [`PULSE`] and pushes it only when the rendered bytes CHANGED. So the
/// waiting seat in a simultaneous-move game learns that the opponent sealed / opened / resolved
/// without touching reload — and, because each frame is the viewer's OWN per-viewer render, the fog
/// is exactly the fog the page was served with (a spectator's stream never carries a sealed move or
/// a hand).
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

// ─────────────────────────────────────────────────────────────────────────────────────────
// THE PAGES
// ─────────────────────────────────────────────────────────────────────────────────────────

/// The block every landing page carries: what a minted table is, and the button that mints one.
pub fn open_a_table_section(lock: &TableLock) -> String {
    format!(
        "<section class=\"panel\"><h2>Open a table</h2>\
         <p class=\"prose\">A table is minted with two seat links. Keep one, send the other — \
         whoever opens a link takes that seat, and nobody else can. There is no shared lobby to \
         race for and no public table to wander into.</p>\
         <p class=\"prose\">Each seat has <strong>{minutes} minutes</strong> to make its move. A \
         seat that lets that run out forfeits the table, so an abandoned match ends instead of \
         waiting forever.</p>\
         <form method=\"post\" action=\"{route}/table\" class=\"affordance\">\
         <button type=\"submit\">Open a table</button></form>\
         </section>",
        minutes = table_seats::turn_limit().as_secs() / 60,
        route = lock.route,
    )
}

/// The lobby page a mint returns — the two seat links plus the spectator link.
fn lobby_page(door: &TableDoor, id: &str) -> String {
    let a = door.lock.seat_link(id, SeatSlot::A);
    let b = door.lock.seat_link(id, SeatSlot::B);
    let body = format!(
        "<main class=\"session af-table\">\
         <div class=\"page-head\" style=\"padding-top:var(--s4)\">\
         <h1>Table opened</h1>\
         <p class=\"deck\">{game} · session <span class=\"sid\">{id}</span> — seat-locked. Only \
         these two links can sit down.</p></div>\
         <section class=\"panel\"><h2>Your link</h2>\
         <p class=\"prose\">Open this one yourself. {seat_note}</p>\
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
         <p class=\"prose\">{spectator_note}</p>\
         <p class=\"invite\"><code>{watch}</code></p>\
         <p><a class=\"seat-link\" href=\"{watch}\">Watch this table →</a></p>\
         </section>\
         <p class=\"prose\"><a class=\"backlink\" href=\"{route}\">← the rules</a></p>\
         </main>",
        game = esc(door.lock.game),
        id = esc(id),
        seat_note = door.seat_note,
        spectator_note = door.spectator_note,
        a = esc(&a),
        b = esc(&b),
        watch = esc(&door.lock.watch_link(id)),
        route = door.lock.route,
    );
    document(
        &format!("{} — table opened", crate::PRODUCT_NAME),
        "offerings",
        &body,
    )
}

/// The page a bad/absent seat key gets — honest, and it points at the thing they CAN do.
fn seat_refused_page(door: &TableDoor, id: &str) -> String {
    let body = format!(
        "<main class=\"session af-table\">\
         <div class=\"notice refused\" role=\"status\">That seat link is not valid for this table. \
         Seat links are minted per table, and on a deployment with no durable session directory \
         they do not survive a server restart.</div>\
         <p class=\"prose\">You can still watch: \
         <a class=\"backlink\" href=\"{watch}\">spectate this table →</a></p>\
         <p class=\"prose\"><a class=\"backlink\" href=\"{route}\">← open your own table</a></p>\
         </main>",
        watch = esc(&door.lock.watch_link(id)),
        route = door.lock.route,
    );
    document(
        &format!("{} — seat refused", crate::PRODUCT_NAME),
        "offerings",
        &body,
    )
}

/// The 303 body (a browser follows the `Location`; this is what a non-following client reads).
fn seat_taken_page(door: &TableDoor, id: &str) -> String {
    let body = format!(
        "<main class=\"session af-table\"><div class=\"notice ok\" role=\"status\">Seat taken — \
         opening the table.</div>\
         <p class=\"prose\"><a class=\"backlink\" href=\"{table}\">Go to the table →</a></p></main>",
        table = esc(&door.lock.table_link(id)),
    );
    document(
        &format!("{} — seat taken", crate::PRODUCT_NAME),
        "offerings",
        &body,
    )
}

fn watch_missing_page(door: &TableDoor, id: &str) -> String {
    let body = format!(
        "<main class=\"session af-table\"><div class=\"notice refused\" role=\"status\">No {key} \
         table at <code>{id}</code>. Watching does not open one — a table exists once somebody \
         mints it.</div>\
         <p class=\"prose\"><a class=\"backlink\" href=\"{route}\">← open a table</a></p>\
         </main>",
        key = esc(door.lock.key),
        id = esc(id),
        route = door.lock.route,
    );
    document(
        &format!("{} — no such table", crate::PRODUCT_NAME),
        "offerings",
        &body,
    )
}

/// The banner a resolved table wears, wherever it is shown. It says what the record IS — a lobby
/// note that a seat stopped playing — and refuses to dress it as a proven result.
pub fn resolution_notice(resolution: &Resolution) -> String {
    format!(
        // ⚑ Every clause is checked. A forfeit lands NO receipt and NO executor turn (this lobby
        // is the only thing that records it), and neither game's rules have a method for it:
        // automatafl's `winner` register is write-once under `resolve`, and the tug's is
        // threshold-gated on `charm ≥ 11 ∨ guilds ≥ 4`. "not a proven win" is pinned by
        // `dreggnet-web/tests/tug_table.rs` and stays verbatim.
        "<div class=\"notice refused\" role=\"status\"><strong>Table over</strong> — {headline}. \
         <br>This is the lobby noting that somebody stopped playing. No move was made and there is \
         no receipt for it: neither game's rules have any way to hand the win to whoever is still \
         sitting there, so it is not a proven win.</div>",
        headline = esc(&resolution.headline()),
    )
}

/// The page a resolved table serves to somebody arriving at a seat link or resigning.
fn resolved_page(door: &TableDoor, id: &str, resolution: &Resolution) -> String {
    let body = format!(
        "<main class=\"session af-table\">\
         <div class=\"page-head\" style=\"padding-top:var(--s4)\"><h1>Table over</h1>\
         <p class=\"deck\">{game} · session <span class=\"sid\">{id}</span></p></div>\
         {notice}\
         <p class=\"prose\">The final position is still readable: \
         <a class=\"backlink\" href=\"{watch}\">look at the table →</a></p>\
         <p class=\"prose\"><a class=\"backlink\" href=\"{route}\">← open a new table</a></p>\
         </main>",
        game = esc(door.lock.game),
        id = esc(id),
        notice = resolution_notice(resolution),
        watch = esc(&door.lock.watch_link(id)),
        route = door.lock.route,
    );
    document(
        &format!("{} — table over", crate::PRODUCT_NAME),
        "offerings",
        &body,
    )
}

/// The spectator page. The live region carries `data-readonly`, and the served surface is wrapped
/// in a `disabled` `<fieldset>` — the HTML-native way to make every descendant control inert, so
/// the read-only rendering needs no parsing of the offering's own markup and cannot drift from it.
///
/// A spectator who re-enables the controls by hand gains nothing they did not already have: their
/// POST would land under the spectator identity, exactly as any anonymous visitor's already can on
/// an ad-hoc table — and on a seat-locked table [`crate::table_seats::enforce`] refuses it outright.
fn spectate_page(
    door: &TableDoor,
    id: &str,
    fragment: &str,
    resolution: Option<&Resolution>,
) -> String {
    let body = format!(
        "<div class=\"crumb\"><a href=\"{route}\">← {game}</a>\
         <span class=\"sep\">·</span><strong>spectating</strong>\
         <span class=\"sep\">·</span><span class=\"sid\">session {id}</span></div>\
         <main class=\"session af-table\">\
         <div class=\"page-head\" style=\"padding-top:var(--s4)\"><h1>Spectating</h1>\
         <p class=\"deck\">{spectator_note}</p></div>\
         {banner}\
         <div id=\"live-surface\" class=\"live-surface spectating\" tabindex=\"-1\" \
         aria-live=\"polite\" data-readonly=\"1\" \
         data-events=\"{watch}/events\">\
         <fieldset class=\"spectate-lock\" disabled>{fragment}</fieldset></div>\
         </main>",
        route = door.lock.route,
        game = esc(door.lock.game),
        id = esc(id),
        spectator_note = door.spectator_note,
        banner = resolution.map(resolution_notice).unwrap_or_default(),
        watch = esc(&door.lock.watch_link(id)),
        fragment = fragment,
    );
    document(
        &format!("{} — spectating {id}", crate::PRODUCT_NAME),
        "offerings",
        &body,
    )
}
