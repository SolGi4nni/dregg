//! # `GET /you` — **the page where a player sees their own games, runs and receipts.**
//!
//! The product's pitch is that every move is a receipt anyone can replay, and The Descent runs a
//! daily board with your name on it. Until this route existed there was **no page a player could go
//! to and see their own side of that**: no `/me`, no `/account`, no `/profile`, no `/stats`. The
//! only identity-shaped endpoint on the whole surface was `/metrics`, which is Prometheus for
//! operators. A player who closed the tab could not find their own table again.
//!
//! This module is deliberately **assembly, not new machinery**. Every number it prints is read out
//! of something that already stores it, and every link it emits points at a page that already
//! exists (`/offerings/{key}/session/{id}`, `.../verify`, `/descent/run/{id}`,
//! `/descent/native/run/{id}`). It adds no store, no cache and no new notion of a player.
//!
//! ## The three joins it can honestly make, and who the third one reaches
//!
//! 1. **The seat join.** A minted automatafl / multiway-tug seat link installs the seat's secret
//!    label as the browser's `dregg_user` cookie ([`crate::table_door`]), and only the holder of
//!    that secret can produce it. So [`crate::table_seats::TableLock::seat_of_label`] over the live
//!    session ids says *exactly* which tables this browser holds a seat at — before a single move
//!    is made, and unforgeably.
//! 2. **The actor join.** A landed catalog turn is logged with the actor it was attributed to
//!    (`blake3(label)`), so the viewer's own landed moves are countable off each session's
//!    [`SessionMoveLog`](dreggnet_offerings::resume::SessionMoveLog).
//! 3. **The board join,** by EXACT label ([`DescentState::runs_for_labels`]).
//!
//! What it cannot do **for an anonymous visitor**: claim the browser-native Descent runs. With no
//! claimed identity, `/descent/play` still signs a run with a pseudonym it mints and keeps in **this
//! tab's `localStorage`** (`dregg.native-descent.actor.v1`) — never with the `dregg_user` cookie —
//! so the server has no way to know that a `web:…` board row is the same person as this cookie, and
//! this page says so in prose instead of quietly showing an empty panel.
//!
//! For a **claimed** identity ([`crate::seed_identity`]) that gap is CLOSED, and it was closed where
//! this doc said it had to be — at the play surface. `/descent/play` now renders the claimed public
//! key into the page and `browserActor()` prefers it over the minted pseudonym, so the actor bound
//! into the native journal chain IS the 64-char identity, which is exactly what `runs_for_labels`
//! matches on below. Nothing about the anonymous path changed.
//!
//! ## Why `?user=` is REFUSED here
//!
//! Everywhere else on the catalog, `?user=` is an honest convenience: it is an *asserted* label and
//! the surface says so. On a page whose entire content is "your games", an attacker-choosable label
//! would be a read of somebody else's shelf. So this route serves a personal page **only** for an
//! ESTABLISHED identity ([`web_user_established`] — the durable cookie, or a `?user=` that merely
//! re-states it) and answers `403` otherwise, with nothing personal in the body.
//!
//! ## What is never printed
//!
//! The `dregg_user` cookie value **is a bearer credential** on this surface: `?user=<that value>`
//! acts as that identity on the act path, and for a table it IS the seat key. So the page prints
//! only its SHAPE (`visitor-…`, `afs1-a-…`) and the one-way `blake3` actor digest — never the label
//! itself.

use std::sync::Arc;

use axum::Router;
use axum::extract::{Query, State};
use axum::http::{HeaderMap, StatusCode};
use axum::middleware;
use axum::response::{Html, IntoResponse, Response};
use axum::routing::get;

use dreggnet_offerings::{DreggIdentity, SessionId};

use crate::descent::BoardRun;
use crate::table_seats::{self, SeatSlot};
use crate::web_identity_http::{self, web_user_established};
use crate::{CatalogState, DescentState, PRODUCT_NAME, WebQuery, document_with_head, esc};

/// The canonical path. `/me` is mounted as an alias because that is the other thing people type.
pub const YOU_PATH: &str = "/you";

/// The axum state — the two stores a player's own record actually lives in.
#[derive(Clone)]
pub struct YouState {
    /// The live catalog host: sessions in progress, their move logs, their replay verification.
    pub catalog: Arc<CatalogState>,
    /// The Descent board: recorded runs, re-verified per read.
    pub descent: Arc<DescentState>,
}

/// **Mount the YOU page.** Additive: `/you` and `/me` overlap nothing. The visitor bootstrap is
/// layered here for the same reason the catalog layers it — a cookie-less first visit must arrive
/// with an established identity rather than being told it is `anon`.
pub fn you_router(catalog: Arc<CatalogState>, descent: Arc<DescentState>) -> Router {
    Router::new()
        .route(YOU_PATH, get(get_you))
        .route("/me", get(get_you))
        .layer(middleware::from_fn(
            web_identity_http::bootstrap_visitor_identity,
        ))
        .with_state(YouState { catalog, descent })
}

// ═══════════════════════════════════════════════════════════════════════════════
// What the page knows.
// ═══════════════════════════════════════════════════════════════════════════════

/// One live catalog session this viewer has a claim on — a table they hold a seat at, or one they
/// have landed a move in. Everything here is read off the host; nothing is stored by this module.
struct MyTable {
    /// The offering key (`automatafl`, `tug`, `descent`, …).
    key: String,
    /// The offering's own display title.
    title: String,
    /// The session id.
    id: String,
    /// The seat this browser holds, when the table was minted through a seat lock.
    seat: Option<SeatSlot>,
    /// Landed turns attributed to this viewer.
    mine: usize,
    /// Landed turns in the whole session (mine plus everyone else's).
    total: usize,
    /// How many of MY turns carried a verified signature rather than an asserted label.
    signed: usize,
    /// The lobby's record of how the table ended, if it has.
    resolved: Option<String>,
    /// The session's replay verification, taken on this read.
    verified: Option<(bool, usize, String)>,
}

impl MyTable {
    fn resume_href(&self) -> String {
        format!("/offerings/{}/session/{}", self.key, self.id)
    }

    fn verify_href(&self) -> String {
        format!("/offerings/{}/session/{}/verify", self.key, self.id)
    }
}

/// A session id plus the counts read on the host's own thread. Kept flat so the closure handed to
/// [`CatalogState::run_offering`] returns plain `Send` data.
struct RawSession {
    id: String,
    mine: usize,
    total: usize,
    signed: usize,
}

/// Collect the viewer's live tables across the ship list.
fn my_tables(state: &YouState, label: &str, me: &DreggIdentity) -> Vec<MyTable> {
    let mut tables = Vec::new();
    for key in dreggnet_catalog::SHIPPED_KEYS {
        let owned_key = key.to_string();
        let actor = me.clone();
        // ONE host job per offering: enumerate its live sessions and count this viewer's landed
        // turns off each log, on the host's own thread.
        let raw: Vec<RawSession> = state.catalog.run_offering(key, me, move |host| {
            host.session_ids(&owned_key)
                .into_iter()
                .map(|id| {
                    let (mine, total, signed) = match host.move_log(&owned_key, &id) {
                        Some(log) => {
                            let total = log.moves.len();
                            let mine = log
                                .moves
                                .iter()
                                .filter(|logged| logged.actor == actor)
                                .count();
                            let signed = log
                                .moves
                                .iter()
                                .filter(|logged| {
                                    logged.actor == actor && logged.attribution.is_signed()
                                })
                                .count();
                            (mine, total, signed)
                        }
                        None => (0, 0, 0),
                    };
                    RawSession {
                        id: id.0,
                        mine,
                        total,
                        signed,
                    }
                })
                .collect()
        });

        let lock = table_seats::lock_for_key(key);
        let title = {
            let owned_key = key.to_string();
            state
                .catalog
                .run_offering(key, me, move |host| {
                    host.title(&owned_key).map(str::to_string)
                })
                .unwrap_or_else(|| key.to_string())
        };

        for session in raw {
            // THE SEAT JOIN — unforgeable: only the holder of the seat secret carries this label.
            let seat = lock
                .filter(|lock| lock.is_locked_table(&session.id))
                .and_then(|lock| lock.seat_of_label(&session.id, label));
            if seat.is_none() && session.mine == 0 {
                continue;
            }
            let resolved = table_seats::registry()
                .resolution(&session.id)
                .map(|resolution| resolution.headline());
            let verified = state
                .catalog
                .verify(key, &SessionId::new(session.id.clone()))
                .map(|report| (report.verified, report.turns, report.detail));
            tables.push(MyTable {
                key: key.to_string(),
                title: title.clone(),
                id: session.id,
                seat,
                mine: session.mine,
                total: session.total,
                signed: session.signed,
                resolved,
                verified,
            });
        }
    }
    // A table you are still owed a move at reads first; then the busiest.
    tables.sort_by(|a, b| {
        a.resolved
            .is_some()
            .cmp(&b.resolved.is_some())
            .then_with(|| b.mine.cmp(&a.mine))
            .then_with(|| a.key.cmp(&b.key))
            .then_with(|| a.id.cmp(&b.id))
    });
    tables
}

// ═══════════════════════════════════════════════════════════════════════════════
// The handler.
// ═══════════════════════════════════════════════════════════════════════════════

/// `GET /you` (and `/me`) — the viewer's own shelf.
async fn get_you(
    State(state): State<YouState>,
    headers: HeaderMap,
    Query(query): Query<WebQuery>,
) -> Response {
    let (label, established) = web_user_established(&headers, &query);
    if !established {
        // ⚑ THE WHOLE POINT OF THIS BRANCH. A `?user=` that the cookie does not back is an
        // attacker-choosable label; on a page made of "your games" it would be a read of someone
        // else's shelf. Nothing personal is gathered, let alone rendered.
        return (
            StatusCode::FORBIDDEN,
            Html(refused_page(query.user.is_some())),
        )
            .into_response();
    }

    // `resolve_identity`, not `web_identity`: a CLAIMED label resolves to the public key itself, so
    // for a phrase-backed player `me.0` is the same 64-char actor the catalog attributes turns to
    // AND the actor `/descent/play` now signs native runs with. That is what makes the board join
    // below finally land for that player — the gap this module's doc named as unclosable from here
    // was closed at the play surface (`descent_play`'s `data-claimed-actor`), not on this page.
    let me = crate::seed_identity::resolve_identity(&label);
    let tables = my_tables(&state, &label, &me);
    // The board is joined on labels this page can stand behind for the viewer: the established
    // cookie label, and the derived actor hex a signed / claimed submitter records. Both are
    // matched EXACTLY by `runs_for_labels`.
    let runs = state
        .descent
        .runs_for_labels(&[label.clone(), me.0.clone()]);

    let mut response = Html(you_page(&label, &me, &tables, &runs)).into_response();
    // Personal, and it changes the moment you move. Never let a shared cache hold it.
    response.headers_mut().insert(
        axum::http::header::CACHE_CONTROL,
        axum::http::HeaderValue::from_static("private, no-store"),
    );
    response
}

// ═══════════════════════════════════════════════════════════════════════════════
// Rendering. The Night Record (`.af-table`) plus a small page-scoped sheet.
// ═══════════════════════════════════════════════════════════════════════════════

/// The page-scoped sheet. It only arranges things the shared skin already paints (plaques with a
/// brass hairline and a thick left accent, the mono voice for verifiable material), so nothing here
/// re-declares a colour token.
const YOU_STYLE: &str = r##"<style>
.you-id{display:grid;grid-template-columns:auto 1fr;gap:.3rem .9rem;margin:.7rem 0 .2rem;font-size:var(--t-sm)}
.you-id dt{color:rgba(237,220,180,.55);font-family:var(--mono);font-size:var(--t-micro);text-transform:uppercase;letter-spacing:.1em;padding-top:.15rem}
.you-id dd{margin:0;color:var(--n-ink);font-family:var(--mono);overflow-wrap:anywhere}
.you-rows{display:flex;flex-direction:column;gap:.5rem;margin:.75rem 0 .2rem}
.you-row{display:flex;flex-wrap:wrap;align-items:baseline;gap:.4rem .7rem;padding:.6rem .8rem;border:1px solid var(--br-faint);border-left:3px solid var(--vio);border-radius:0 10px 10px 10px;background:rgba(7,6,11,.5)}
.you-row.is-over{border-left-color:rgba(164,159,180,.45)}
.you-row .what{font-family:var(--n-serif);font-size:var(--t-lead);font-weight:600;color:var(--br-pale);flex:1 1 12rem;margin:0}
.you-row .meta{margin:0;flex:1 1 100%;font-family:var(--mono);font-size:var(--t-micro);color:var(--n-soft);letter-spacing:.02em;overflow-wrap:anywhere}
.you-row .said{margin:.15rem 0 0;flex:1 1 100%;color:var(--n-soft);font-size:var(--t-sm)}
.you-row .go{font-weight:700;font-size:var(--t-sm);white-space:nowrap}
.you-empty{margin:.6rem 0 .1rem;color:var(--n-soft)}
.you-empty strong{color:var(--br-pale)}
.you-doors{display:flex;flex-wrap:wrap;gap:.5rem;margin:.7rem 0 .1rem}
</style>"##;

/// The one-line "what this page is" plaque plus every panel.
fn you_page(label: &str, me: &DreggIdentity, tables: &[MyTable], runs: &[BoardRun]) -> String {
    let body = format!(
        "<main class=\"session af-table you-page\">\
         <div class=\"page-head\"><p class=\"eyebrow\">Your own record</p><h1>You</h1>\
         <p class=\"deck\">Everything this server can honestly say is yours: the tables it is \
         holding open for you, the runs the board has under your name, and the receipts your own \
         moves minted. Every link here goes to the page that re-runs the thing rather than to a \
         copy of its result.</p></div>\
         {identity}{tables}{runs}{receipts}\
         <p class=\"prose\"><a class=\"backlink\" href=\"/offerings\">← All games</a></p>\
         </main>",
        identity = identity_panel(label, me),
        tables = tables_panel(tables),
        runs = runs_panel(label, runs),
        receipts = receipts_panel(tables),
    );
    document_with_head(
        &format!("{PRODUCT_NAME} — you"),
        "you",
        &format!("{YOU_STYLE}{LOCAL_RUN_SCRIPT}"),
        &body,
    )
}

/// The shape of an identity label, with no secret in it. `visitor-…`, `afs1-a-…`, `alice`.
///
/// The full label is NEVER printed: on this surface it is a bearer credential (`?user=<label>` acts
/// as that identity), and for a minted table it is literally the seat key.
fn label_shape(label: &str) -> String {
    // A CLAIM label is `<prefix><pubkey>.<mac>`; the public key half is already printed as the actor
    // below, and the mac half is the credential. Detected through the owner's own parser rather than
    // by matching its prefix string, so a change to that format cannot silently start printing macs.
    if crate::seed_identity::parse_claim_label(label).is_some() {
        return "a claimed identity …".to_string();
    }
    for prefix in ["visitor-", "afs1-a-", "afs1-b-", "tugs1-a-", "tugs1-b-"] {
        if label.starts_with(prefix) {
            return format!("{prefix}…");
        }
    }
    // An explicitly asserted short name (`alice`) is the thing the operator typed, not a minted
    // secret; anything long enough to be a minted label is still shortened.
    if label.len() > 12 {
        format!("{}…", &label[..8])
    } else {
        label.to_string()
    }
}

/// What KIND of identity this is, in a sentence — the honest description of its durability.
fn identity_kind(label: &str) -> &'static str {
    if crate::seed_identity::parse_claim_label(label).is_some() {
        "a CLAIMED identity — a public key you hold the 24 words for. It is the one identity on \
         this surface that survives a cleared cookie: the words reproduce it on any device, so the \
         record below is yours rather than this browser's."
    } else if table_seats::ALL
        .iter()
        .any(|lock| label.starts_with(lock.seat_prefix))
    {
        "a TABLE SEAT. Taking a seat link replaced this browser's ordinary visitor label with the \
         seat's own secret, so while you hold this seat it is who you are on every page — including \
         this one."
    } else if label.starts_with("visitor-") {
        "a visitor label this server minted for this browser the first time it arrived. It is a \
         name, not a login: nothing was proved and nothing is recoverable."
    } else {
        "a label that was asserted explicitly rather than minted here. It is taken at face value."
    }
}

fn identity_panel(label: &str, me: &DreggIdentity) -> String {
    let actor_short: String = me.0.chars().take(16).collect();
    // The durability paragraph BRANCHES, because the honest answer now differs. A claimed identity
    // is recoverable and this page must not keep saying it is not; an unclaimed one is exactly as
    // fragile as it always was, and the fix is one link away rather than unavailable.
    let durability = if crate::seed_identity::parse_claim_label(label).is_some() {
        "<p class=\"prose\"><strong>How durable is this?</strong> Recoverable. This identity is a \
         public key derived from 24 words you wrote down, so clearing your cookies or moving to \
         another device costs you nothing you cannot type back — everything below is filed under \
         the key, not under this browser. What it still is <em>not</em>: a signature. Your moves \
         are attributed to your key, not signed by it, because neither this page nor the server \
         holds the secret. A tool that holds your phrase can sign as you; see \
         <a href=\"/identity\">your identity</a>.</p>"
    } else {
        "<p class=\"prose\"><strong>How durable is this?</strong> It is a cookie. Clear your \
         cookies, switch browsers, or open a private window and you are a new person here, with \
         <em>no recovery</em> — the games above would not be reachable from the new identity and \
         nothing on this page could hand them back. That is fixable and opt-in: \
         <a href=\"/identity\">claim a recoverable identity</a> and you get 24 words that reproduce \
         this player anywhere. You do not have to, and nothing stops working if you never do.</p>\
         <p class=\"prose\">Your moves are attributed by that label, not signed by a key you hold — \
         which is why every receipt below says <em>asserted</em>. The proof on this surface is that \
         the move was re-run against the rules, not that a particular human made it.</p>"
    };
    format!(
        "<section class=\"deos-section tag-accent\"><h2>Who you are here</h2>\
         <p class=\"prose\">You are {kind}</p>\
         <dl class=\"you-id\">\
         <dt>your label</dt><dd>{shape} <span class=\"you-empty\">(not printed in full — on this \
         surface the label itself acts as the credential)</span></dd>\
         <dt>actor</dt><dd>{actor}…</dd>\
         </dl>{durability}</section>",
        kind = identity_kind(label),
        shape = esc(&label_shape(label)),
        actor = esc(&actor_short),
        durability = durability,
    )
}

/// The seat line for a table, or the plain "you have moved here" line.
fn table_meta(table: &MyTable) -> String {
    let mut parts: Vec<String> = Vec::new();
    if let Some(seat) = table.seat {
        parts.push(format!("seat {}", seat.label()));
    }
    parts.push(format!("session {}", table.id));
    parts.push(format!(
        "{mine} of {total} landed turn{s} yours",
        mine = table.mine,
        total = table.total,
        s = if table.total == 1 { "" } else { "s" },
    ));
    parts.push(if table.signed > 0 {
        format!("{} signed", table.signed)
    } else {
        "asserted attribution".to_string()
    });
    if let Some((verified, turns, _)) = &table.verified {
        parts.push(if *verified {
            format!("chain re-verified by replay over {turns} turns")
        } else {
            "chain does NOT re-verify".to_string()
        });
    }
    esc(&parts.join(" · "))
}

fn tables_panel(tables: &[MyTable]) -> String {
    if tables.is_empty() {
        return format!(
            "<section class=\"deos-section tag-muted\"><h2>Games in progress</h2>\
             <p class=\"you-empty\"><strong>Nothing is waiting for you.</strong> You have not \
             opened a table yet — or the one you opened has been released (this server holds a \
             table only while somebody is at it). Nothing has been lost that this page is hiding: \
             there is genuinely no game here with your name on it.</p>\
             <p class=\"you-empty\">Start one, and it will appear here the moment it exists:</p>\
             {doors}</section>",
            doors = doors_html(),
        );
    }
    let rows: String = tables
        .iter()
        .map(|table| {
            format!(
                "<div class=\"you-row{over}\">\
                 <p class=\"what\">{title}</p>\
                 <a class=\"go\" href=\"{resume}\">{verb} →</a>\
                 <p class=\"meta\">{meta}</p>\
                 {said}\
                 <p class=\"meta\"><a href=\"{verify}\" rel=\"nofollow\">Replay-verify this \
                 chain</a></p>\
                 </div>",
                over = if table.resolved.is_some() {
                    " is-over"
                } else {
                    ""
                },
                title = esc(&table.title),
                resume = esc(&table.resume_href()),
                verb = if table.resolved.is_some() {
                    "Look at it"
                } else {
                    "Back to the table"
                },
                meta = table_meta(table),
                said = table
                    .resolved
                    .as_deref()
                    .map(|headline| format!(
                        "<p class=\"said\">This table is over — {}. No executor turn backs that: \
                         it is the lobby's record of an abandoned table, not a proven win.</p>",
                        esc(headline)
                    ))
                    .unwrap_or_default(),
                verify = esc(&table.verify_href()),
            )
        })
        .collect();
    format!(
        "<section class=\"deos-section tag-accent\"><h2>Games in progress</h2>\
         <p class=\"prose\">{count} table{s} here {is} yours — because you hold a minted seat at \
         it, or because a move of yours landed in it. Closing the tab never ended any of them.</p>\
         <div class=\"you-rows\">{rows}</div></section>",
        count = tables.len(),
        s = if tables.len() == 1 { "" } else { "s" },
        is = if tables.len() == 1 { "is" } else { "are" },
        rows = rows,
    )
}

fn doors_html() -> String {
    "<p class=\"you-doors\">\
     <a class=\"btn btn-primary\" href=\"/descent/play\">Play The Descent <span class=\"arr\" \
     aria-hidden=\"true\">→</span></a>\
     <a class=\"btn btn-ghost\" href=\"/automatafl\">Open an Automatafl table</a>\
     <a class=\"btn btn-ghost\" href=\"/tug\">Open a Multiway-Tug table</a>\
     </p>"
        .to_string()
}

/// **Why a board run might not be claimable for this viewer** — and it is NOT the same answer for
/// everyone, which is exactly why this is branched rather than a fixed paragraph. An unclaimed
/// browser signs its Descent runs with a pseudonym kept in that tab's own storage, so the server has
/// nothing linking those rows to the cookie. A CLAIMED browser signs them with the claimed public
/// key (`descent_play`'s `data-claimed-actor` → `browserActor()`), which is precisely the label the
/// board join matches — so for that reader the only unreachable runs are the ones played BEFORE the
/// claim. Saying the first sentence to the second reader would be a stale, honest-sounding lie.
fn why_the_board_may_not_know_you(label: &str) -> &'static str {
    if crate::seed_identity::parse_claim_label(label).is_some() {
        "<p class=\"you-empty\">Runs you play from now on <em>will</em> land here: because this \
         identity is claimed, the play surface signs a run with your public key rather than with a \
         throwaway browser name, and that key is exactly what the board is searched for above. A \
         run you finished <em>before</em> claiming still carries the old browser-local name, and \
         nothing links the two — the panel below reads that name out of this tab so you can still \
         recognise that row.</p>"
    } else {
        "<p class=\"you-empty\">There is a second reason, and it is ours, not yours: an unclaimed \
         browser signs its runs with a pseudonym <em>that tab keeps in its own local storage</em>, \
         never with the cookie above. So even a run of yours sitting on today's board cannot be \
         claimed for you from the server side — the two names have nothing linking them. \
         <a href=\"/identity\">Claiming an identity</a> fixes it going forward, because the play \
         surface then signs with your key; the panel below reads the browser-local name out of this \
         tab either way, so you can recognise your own row on the board.</p>"
    }
}

fn runs_panel(label: &str, runs: &[BoardRun]) -> String {
    if runs.is_empty() {
        return format!(
            "<section class=\"deos-section tag-muted\"><h2>Finished Descent runs</h2>\
             <p class=\"you-empty\"><strong>The board has no run under this label.</strong> If you \
             have never finished a descent, that is simply why — the board only holds runs that were \
             submitted and re-verified, and yours would appear here the moment one is.</p>\
             {why}\
             {local}\
             <p class=\"you-empty\">The day's board is at <a href=\"/descent\">/descent</a>.</p>\
             </section>",
            why = why_the_board_may_not_know_you(label),
            local = local_run_slot(),
        );
    }
    let rows: String = runs
        .iter()
        .map(|run| {
            let verdict = match (run.verified, run.finished) {
                (true, true) => "re-verified · finished".to_string(),
                (true, false) => "re-verified · did not finish".to_string(),
                (false, _) => "DOES NOT re-execute".to_string(),
            };
            let mut parts = vec![
                format!("day {}", run.day_key),
                format!(
                    "{lane} lane",
                    lane = if run.native { "native" } else { "board" }
                ),
                format!("{} turns", run.turns),
                format!("depth {}", run.depth),
            ];
            if run.relics > 0 {
                parts.push(format!("{} relics banked", run.relics));
            }
            parts.push(verdict);
            format!(
                "<div class=\"you-row{over}\"><p class=\"what\">Run {id}</p>\
                 <a class=\"go\" href=\"{path}\">Replay it →</a>\
                 <p class=\"meta\">{meta}</p></div>",
                over = if run.verified { "" } else { " is-over" },
                id = esc(&run.run_id),
                path = esc(&run.path),
                meta = esc(&parts.join(" · ")),
            )
        })
        .collect();
    format!(
        "<section class=\"deos-section tag-accent\"><h2>Finished Descent runs</h2>\
         <p class=\"prose\">{count} run{s} on the board carr{y} your label. Each verdict here was \
         taken by re-executing the run just now — none of it is a stored flag.</p>\
         <div class=\"you-rows\">{rows}</div>{local}</section>",
        count = runs.len(),
        s = if runs.len() == 1 { "" } else { "s" },
        y = if runs.len() == 1 { "ies" } else { "y" },
        rows = rows,
        local = local_run_slot(),
    )
}

/// The slot the page-scoped script fills from this tab's own storage. Server-rendered with the
/// honest fallback, so a reader with no JS is told what the panel would have said instead of seeing
/// a blank.
fn local_run_slot() -> String {
    "<div class=\"you-rows\" id=\"you-local-descent\" \
     data-empty=\"This tab has no Descent run saved in it.\">\
     <p class=\"you-empty\" id=\"you-local-note\">This browser keeps its own Descent name and its \
     unfinished run in local storage. Reading that needs JavaScript; with it off, \
     <a href=\"/descent/play\">/descent/play</a> is still the page that holds them.</p></div>"
        .to_string()
}

/// Read this tab's own Descent pseudonym and retained run out of `localStorage` and say what is
/// there. **No request is made** — the keys are exactly the ones `/descent/play` writes, and every
/// value lands in a text node, never in markup.
const LOCAL_RUN_SCRIPT: &str = r##"<script>
(function(){
  "use strict";
  var ACTOR="dregg.native-descent.actor.v1";
  var RECORD="dregg.native-descent.record.v1:";
  function ready(fn){
    if(document.readyState!=="loading")fn();
    else document.addEventListener("DOMContentLoaded",fn);
  }
  ready(function(){
    var slot=document.getElementById("you-local-descent");
    var note=document.getElementById("you-local-note");
    if(!slot||!note)return;
    var store;
    try{store=window.localStorage;}catch(e){return;}
    if(!store)return;
    var actor=null;
    try{actor=store.getItem(ACTOR);}catch(e){actor=null;}
    var runs=[];
    try{
      for(var i=0;i<store.length;i++){
        var key=store.key(i);
        if(!key||key.indexOf(RECORD)!==0)continue;
        var raw=store.getItem(key);
        if(!raw)continue;
        var rec=null;
        try{rec=JSON.parse(raw);}catch(e){continue;}
        if(!rec||typeof rec!=="object")continue;
        runs.push({
          day:key.slice(RECORD.length),
          moves:Array.isArray(rec.events)?rec.events.length:0,
          done:!!rec.completion
        });
      }
    }catch(e){}
    if(!actor&&runs.length===0){
      note.textContent=slot.getAttribute("data-empty")+" Nothing has been played in this browser \
yet, so there is no local name and no unfinished run to resume.";
      return;
    }
    var lines=[];
    if(actor){
      lines.push("This browser plays The Descent as "+actor+". That is the name your row on the \
board carries — it lives in this tab, not on the server, so clearing site data loses it.");
    }
    slot.innerHTML="";
    lines.forEach(function(text){
      var p=document.createElement("p");
      p.className="you-empty";
      p.appendChild(document.createTextNode(text));
      slot.appendChild(p);
    });
    runs.sort(function(a,b){return b.moves-a.moves;});
    runs.forEach(function(run){
      var row=document.createElement("div");
      row.className="you-row";
      var what=document.createElement("p");
      what.className="what";
      what.appendChild(document.createTextNode(run.done?"A finished run, held in this browser":"An unfinished run, held in this browser"));
      row.appendChild(what);
      var go=document.createElement("a");
      go.className="go";
      go.setAttribute("href","/descent/play");
      go.appendChild(document.createTextNode(run.done?"Open it →":"Resume it →"));
      row.appendChild(go);
      var meta=document.createElement("p");
      meta.className="meta";
      meta.appendChild(document.createTextNode("day "+run.day+" · "+run.moves+" landed move"+(run.moves===1?"":"s")+" · restored only after exact replay"));
      row.appendChild(meta);
      slot.appendChild(row);
    });
    if(runs.length===0){
      var p=document.createElement("p");
      p.className="you-empty";
      p.appendChild(document.createTextNode("No unfinished run is saved in this browser."));
      slot.appendChild(p);
    }
  });
})();
</script>"##;

fn receipts_panel(tables: &[MyTable]) -> String {
    let mine: usize = tables.iter().map(|table| table.mine).sum();
    if mine == 0 {
        return "<section class=\"deos-section tag-muted\"><h2>Your receipts</h2>\
                <p class=\"you-empty\"><strong>No receipt carries your name yet.</strong> A receipt \
                is minted by a move that <em>landed</em> — the executor re-ran it against the rules \
                and accepted it. You have not made one on this identity, so there is nothing here \
                to replay. Make a single move in any game above and this panel fills in.</p>\
                <p class=\"you-empty\">This is the product's own claim, and it is worth knowing \
                what it does and does not cover: the chain of a session re-executes here, in this \
                server, from its recorded moves. That is a real re-run, not a stored verdict — and \
                it is not a blockchain, not a proof carried off this box, and not evidence about \
                <em>who</em> moved, because a browser move is attributed by an asserted label \
                rather than signed by a key you hold.</p></section>"
            .to_string();
    }
    let rows: String = tables
        .iter()
        .filter(|table| table.mine > 0)
        .map(|table| {
            let (verified, turns) = table
                .verified
                .as_ref()
                .map(|(verified, turns, _)| (*verified, *turns))
                .unwrap_or((false, 0));
            format!(
                "<div class=\"you-row{over}\"><p class=\"what\">{title}</p>\
                 <a class=\"go\" href=\"{verify}\" rel=\"nofollow\">Replay-verify →</a>\
                 <p class=\"meta\">{mine} receipt{s} yours · {verdict} · session {id}</p></div>",
                over = if verified { "" } else { " is-over" },
                title = esc(&table.title),
                verify = esc(&table.verify_href()),
                mine = table.mine,
                s = if table.mine == 1 { "" } else { "s" },
                verdict = if verified {
                    format!("the whole chain re-executes over {turns} turns")
                } else {
                    "the chain does NOT re-execute".to_string()
                },
                id = esc(&table.id),
            )
        })
        .collect();
    format!(
        "<section class=\"deos-section tag-accent\"><h2>Your receipts</h2>\
         <p class=\"prose\">{mine} landed turn{s} of yours minted a receipt. Each link below \
         re-executes that session's whole committed chain from its recorded moves, right now — the \
         same replay the leaderboard and the run cards run, not a stored verdict.</p>\
         <div class=\"you-rows\">{rows}</div>\
         <p class=\"you-empty\">What this does not claim: nothing here proves <em>who</em> moved. \
         A browser turn is attributed by an asserted label, so a receipt says \"this move was legal \
         and it landed in this order\", never \"this human made it\".</p></section>",
        mine = mine,
        s = if mine == 1 { "" } else { "s" },
        rows = rows,
    )
}

/// The `403` body. It carries NO personal material — not the asserted label's data, not the
/// cookie's. It exists to explain the refusal, and to point at the page that IS yours.
fn refused_page(asserted: bool) -> String {
    let body = format!(
        "<main class=\"session af-table you-page\">\
         <div class=\"notice refused\" role=\"status\">This page is not readable for an asserted \
         identity.</div>\
         <div class=\"page-head\"><h1>Not your page</h1>\
         <p class=\"deck\">{why}</p></div>\
         <section class=\"deos-section tag-accent\"><h2>Why the refusal is flat</h2>\
         <p class=\"prose\">Everywhere else on this surface a <code>?user=</code> label is an \
         honest convenience: it is <em>asserted</em>, the page says so, and it buys nothing a \
         stranger could not already do. Here the whole content is \"your games\", so honouring an \
         asserted label would be handing out somebody else's shelf to anyone who guessed their \
         name. There is nothing to soften: no part of this page was assembled for that label.</p>\
         <p class=\"prose\">Drop the <code>?user=</code> and <a href=\"{path}\">{path}</a> shows \
         the identity this browser actually holds.</p></section>\
         <p class=\"prose\"><a class=\"backlink\" href=\"/offerings\">← All games</a></p>\
         </main>",
        why = if asserted {
            "You asked for a named identity's page. Nothing in this request proves you are that \
             identity — a <code>?user=</code> label is a claim, not a credential — so this page \
             was not built for it at all."
        } else {
            "This request carries no identity this server established, so there is no \"you\" to \
             show. Visit any page normally first: the server hands a cookie-less browser its own \
             durable visitor label on arrival."
        },
        path = YOU_PATH,
    );
    document_with_head(
        &format!("{PRODUCT_NAME} — not your page"),
        "you",
        YOU_STYLE,
        &body,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_label_is_never_printed_in_full() {
        let seat = "afs1-a-0123456789abcdef0123456789abcdef";
        let shape = label_shape(seat);
        assert_eq!(shape, "afs1-a-…");
        assert!(
            !shape.contains("0123"),
            "the seat secret's random tail must not survive into the shape: {shape}"
        );
        assert_eq!(label_shape("visitor-deadbeef"), "visitor-…");
        // A CLAIM label's mac half is a credential too, and its shape carries none of it.
        let claimed = crate::seed_identity::claim_label(&"ab".repeat(32));
        let shape = label_shape(&claimed);
        let mac = claimed
            .rsplit('.')
            .next()
            .expect("a claim label carries a mac");
        assert!(
            !shape.contains(mac),
            "the claim mac reached the page: {shape}"
        );
        // A short operator-typed name is not a minted secret and stays legible.
        assert_eq!(label_shape("alice"), "alice");
        // Anything long enough to be a minted label is shortened even without a known prefix.
        assert_eq!(label_shape("0123456789abcdef"), "01234567…");
    }

    #[test]
    fn the_identity_sentence_names_the_seat_case_rather_than_calling_it_a_visitor() {
        assert!(identity_kind("afs1-b-ff").contains("TABLE SEAT"));
        assert!(identity_kind("tugs1-a-ff").contains("TABLE SEAT"));
        assert!(identity_kind("visitor-ff").contains("minted"));
        assert!(identity_kind("alice").contains("asserted"));
    }

    #[test]
    fn every_empty_state_says_what_is_empty_in_prose() {
        let tables = tables_panel(&[]);
        assert!(tables.contains("Nothing is waiting for you"), "{tables}");
        assert!(
            tables.contains("/descent/play"),
            "an empty shelf must point at a way to start: {tables}"
        );
        let runs = runs_panel("visitor-abc", &[]);
        assert!(
            runs.contains("The board has no run under this label"),
            "{runs}"
        );
        assert!(
            runs.contains("local storage"),
            "the empty run panel must name the real reason: {runs}"
        );
        let receipts = receipts_panel(&[]);
        assert!(
            receipts.contains("No receipt carries your name yet"),
            "{receipts}"
        );
        // No panel may render as an unexplained blank.
        for panel in [&tables, &runs, &receipts] {
            assert!(panel.contains("you-empty"), "{panel}");
        }
    }

    #[test]
    fn the_refusal_page_explains_itself_and_carries_nothing_personal() {
        let page = refused_page(true);
        assert!(page.contains("Not your page"), "{page}");
        assert!(page.contains("a claim, not a credential"), "{page}");
        // No shelf MARKUP and no shelf PANEL — checked on the row element and the panel headings,
        // not on the class name, which the page's own stylesheet legitimately mentions.
        assert!(
            !page.contains("<div class=\"you-row"),
            "a shelf row was rendered on a refusal: {page}"
        );
        for panel in [
            "Games in progress",
            "Finished Descent runs",
            "Your receipts",
        ] {
            assert!(
                !page.contains(panel),
                "the `{panel}` panel was assembled for a label this page refused: {page}"
            );
        }
    }

    #[test]
    fn identity_durability_is_stated_without_a_promise() {
        let panel = identity_panel("visitor-abc", &crate::web_identity("visitor-abc"));
        assert!(panel.contains("no recovery"), "{panel}");
        assert!(panel.contains("Clear your cookies"), "{panel}");
        // The label itself must never reach the page.
        assert!(!panel.contains("visitor-abc"), "{panel}");
        // …and the way OUT of that fragility is offered rather than merely lamented.
        assert!(panel.contains("/identity"), "{panel}");
    }

    /// The durability paragraph is BRANCHED, and the claimed branch must not keep telling a player
    /// with 24 words in their pocket that they have "no recovery" — a stale honest-sounding
    /// sentence is the wound, not the absence of one.
    #[test]
    fn a_claimed_identity_is_described_as_recoverable() {
        let pubkey_hex =
            crate::seed_identity::derive_pubkey_hex(&dregg_sdk::mnemonic::generate_mnemonic())
                .expect("a generated phrase derives");
        let label = crate::seed_identity::claim_label(&pubkey_hex);
        let panel = identity_panel(&label, &crate::seed_identity::resolve_identity(&label));
        assert!(panel.contains("Recoverable"), "{panel}");
        assert!(!panel.contains("no recovery"), "{panel}");
        assert!(panel.contains("CLAIMED identity"), "{panel}");
        // Still honest about the one thing a claim does NOT buy on this surface.
        assert!(panel.contains("not signed by it"), "{panel}");
        assert!(
            panel.contains("neither this page nor the server holds"),
            "{panel}"
        );
        // The credential (the mac'd label) still never reaches the page.
        assert!(!panel.contains(&label), "{panel}");
    }

    /// The same staleness trap, one panel over: the empty-runs panel used to tell EVERY reader that
    /// the board could never know them, which stopped being true the moment `/descent/play` began
    /// signing with a claimed key. The two branches must not print each other's sentence.
    #[test]
    fn the_empty_runs_reason_is_branched_on_whether_the_identity_is_claimed() {
        let unclaimed = why_the_board_may_not_know_you("visitor-abc");
        assert!(unclaimed.contains("local storage"), "{unclaimed}");
        assert!(unclaimed.contains("/identity"), "{unclaimed}");

        let pubkey_hex =
            crate::seed_identity::derive_pubkey_hex(&dregg_sdk::mnemonic::generate_mnemonic())
                .expect("a generated phrase derives");
        let claimed =
            why_the_board_may_not_know_you(&crate::seed_identity::claim_label(&pubkey_hex));
        assert!(
            claimed.contains("will</em> land here"),
            "a claimed reader must be told their future runs DO land here: {claimed}"
        );
        assert!(
            !claimed.contains("cannot be claimed for you"),
            "the stale sentence survived into the claimed branch: {claimed}"
        );
    }
}
