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
//! ## ⚑ What it had to CUT, and what closed it
//!
//! This page shipped without **finished automatafl / tug history**, for a reason that was in the
//! plumbing rather than in the page: the table registry was an in-process `HashMap` (so a restart
//! forgot that a match was over) and `OfferingHost::close` **DELETED** the durable move-log. On a
//! product whose pitch is that a finished game can be replayed by anyone, the moment a match became
//! that artifact was the moment its only reproducible record was destroyed.
//!
//! Both are closed at the source rather than papered over here:
//!
//! * `close` now **ARCHIVES** the log ([`dreggnet_offerings::SessionResumeStore::archive`]) — held out
//!   of the boot-resume set, so a finished match never comes back as a game in progress, and readable
//!   so [`dreggnet_offerings::OfferingHost::replay_archived`] can re-drive it through the real
//!   executor. `/offerings/{key}/session/{id}/verify` falls back to exactly that, so a finished match
//!   verifies at the same url it always did;
//! * [`crate::table_seats`] now **persists its write-once resolution**, so how a match ended survives
//!   the restart its seat links already survived — which also closed a fail-open (a resolved table
//!   used to start taking acts again after a restart).
//!
//! The panel below is therefore still *assembly*: its `FinishedMatch` rows read the archived log and
//! the persisted ending, and invent no per-match store of their own.
//!
//! ## The four joins it can honestly make
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
//! 4. **The LINK join** ([`crate::identity_link`]). A claimed identity that has proven control of a
//!    Discord / Telegram account has a signed record saying so, so this page can honestly count
//!    *that* account's tables and runs as the same player's. ⚑ It widens the view ONLY through
//!    [`identity_link::linked_actor_keys`], i.e. only to bindings the phrase-holder's own root key
//!    signed — never from a `?user=`, never from a prefix, never from a guess. An unlinked or
//!    unclaimed viewer gets an empty widening, so both those paths render byte-identically to before.
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
use crate::identity_link::{self, LinkedPlatform, WEB_PLATFORM};
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
    /// Landed turns attributed to this viewer — across EVERY identity this page can stand behind
    /// for them (their own, plus any provably linked platform key).
    mine: usize,
    /// Landed turns in the whole session (mine plus everyone else's).
    total: usize,
    /// How many of MY turns carried a verified signature rather than an asserted label.
    signed: usize,
    /// How many of [`mine`](MyTable::mine) landed under a LINKED platform identity rather than under
    /// this browser's own. Carried so the page can say which side of the link a turn came from
    /// instead of silently presenting two custodies as one.
    via_linked: usize,
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

    /// **The spectator link for this table**, when it is a seat-locked one — the thing a player
    /// actually wants from this page and could not get anywhere else: the lobby that minted the table
    /// printed the watch link once, on a page nobody returns to. `None` for an ad-hoc session and
    /// for every non-lockable key (the same guard the session route uses). It carries no secret —
    /// only the table id, which this row already shows.
    fn watch_href(&self) -> Option<String> {
        Some(
            crate::table_seats::lock_for_key(&self.key)
                .filter(|lock| lock.is_locked_table(&self.id))?
                .watch_link(&self.id),
        )
    }
}

/// A session id plus the counts read on the host's own thread. Kept flat so the closure handed to
/// [`CatalogState::run_offering`] returns plain `Send` data.
struct RawSession {
    id: String,
    mine: usize,
    total: usize,
    signed: usize,
    via_linked: usize,
}

/// ⚑ **ONE FINISHED MATCH** — a game that is OVER, read off its archived move-log.
///
/// This panel is the gap this page shipped with. It could show games in progress and Descent runs,
/// and had to CUT finished automatafl / tug history because nothing stored it: the table registry was
/// an in-process `HashMap` and `OfferingHost::close` DELETED the durable log, so the moment a match
/// became the artifact the product's pitch is about was the moment its only reproducible record was
/// destroyed.
///
/// Both halves of that are closed, and this type is the join over the result:
///
/// * the **log** is now archived rather than deleted ([`dreggnet_offerings::SessionResumeStore::archive`]),
///   and it is the whole source of the numbers here — the offering key, the session id, and every
///   landed turn with the actor it was attributed to. No new per-match store was invented for the
///   page; the same reproducible input that makes the match replayable is what makes it listable;
/// * how it **ENDED** comes from the table registry, which now persists its write-once resolution, so
///   a restart no longer forgets that a match is over.
///
/// What this type deliberately does NOT carry is a verdict. Listing a hundred finished matches would
/// mean re-executing a hundred tapes on a page view, so the verdict is taken where it belongs — on
/// the per-match verify page, which re-drives the archived log through the real executor on open.
/// Every row links there rather than printing a stored bit.
struct FinishedMatch {
    /// The offering key (`automatafl`, `tug`, …).
    key: String,
    /// The offering's display title.
    title: String,
    /// The session id.
    id: String,
    /// The seat this browser holds. Derived from the seat key + id exactly as for a live table, so it
    /// works on a finished match with no registry entry at all — and fails CLOSED if the server's
    /// seat key was rotated since (the seat simply stops being claimable, never mis-claimed).
    seat: Option<SeatSlot>,
    /// Landed turns in the archived tape attributed to this viewer (own identity or a linked one).
    mine: usize,
    /// Landed turns in the whole archived tape.
    total: usize,
    /// How many of the viewer's turns carried a verified signature.
    signed: usize,
    /// How many landed under a LINKED platform identity rather than this browser's own.
    via_linked: usize,
    /// How the lobby recorded the ending, if it recorded one.
    ended: Option<String>,
    /// Whether that ending was the match PLAYING ITSELF OUT rather than somebody walking away.
    concluded: bool,
}

impl FinishedMatch {
    /// The page that RE-EXECUTES this match. Not a new route: the ordinary per-session verify route
    /// now falls back to the archive, so a finished match verifies at the same url it always did.
    fn verify_href(&self) -> String {
        format!("/offerings/{}/session/{}/verify", self.key, self.id)
    }
}

/// One archived session's counts, read on the host's own thread and returned flat (`Send`).
struct RawArchived {
    key: String,
    title: String,
    id: String,
    mine: usize,
    total: usize,
    signed: usize,
    via_linked: usize,
}

/// The offering key used ONLY to route the archive read to the SHARED catalog host.
///
/// [`CatalogState::run_offering`] dispatches on whether the key is an RPG key: everything else runs
/// against the one shared host, which is where every seat-locked table lives. A per-identity RPG
/// world's archive is therefore out of scope here on purpose — an inventory is not a match, and each
/// player's world is a different host with a different store.
const SHARED_HOST_ROUTING_KEY: &str = "automatafl";

/// **Every FINISHED match this viewer has a claim on.** One host job: enumerate the archive, count
/// this viewer's landed turns off each archived tape, and hand back flat rows.
fn my_finished_matches(
    state: &YouState,
    label: &str,
    me: &DreggIdentity,
    linked: &[DreggIdentity],
) -> Vec<FinishedMatch> {
    let actor = me.clone();
    let also = linked.to_vec();
    let raw: Vec<RawArchived> =
        state
            .catalog
            .run_offering(SHARED_HOST_ROUTING_KEY, me, move |host| {
                // The titles come off the SAME host in the SAME job, so a finished match is never
                // labelled with a key where a live one gets a name.
                let titles: std::collections::BTreeMap<String, String> = host
                    .list_offerings()
                    .into_iter()
                    .map(|info| (info.key, info.title))
                    .collect();
                host.archived_logs()
                    .into_iter()
                    .map(|log| {
                        let (mut mine, mut signed, mut via_linked) = (0usize, 0usize, 0usize);
                        for logged in &log.moves {
                            let is_own = logged.actor == actor;
                            let is_linked = also.contains(&logged.actor);
                            if !is_own && !is_linked {
                                continue;
                            }
                            mine += 1;
                            if logged.attribution.is_signed() {
                                signed += 1;
                            }
                            if is_linked {
                                via_linked += 1;
                            }
                        }
                        let title = titles
                            .get(&log.key)
                            .cloned()
                            .unwrap_or_else(|| log.key.clone());
                        let total = log.moves.len();
                        RawArchived {
                            key: log.key,
                            title,
                            id: log.id.0,
                            mine,
                            total,
                            signed,
                            via_linked,
                        }
                    })
                    .collect()
            });

    let mut finished: Vec<FinishedMatch> = Vec::new();
    for archived in raw {
        // THE SEAT JOIN, unchanged and still unforgeable — the label is derived under the server key,
        // so only its holder can present it, archive or no archive.
        let seat = table_seats::lock_for_key(&archived.key)
            .filter(|lock| lock.is_locked_table(&archived.id))
            .and_then(|lock| lock.seat_of_label(&archived.id, label));
        if seat.is_none() && archived.mine == 0 {
            continue;
        }
        let resolution = table_seats::registry().resolution(&archived.id);
        finished.push(FinishedMatch {
            key: archived.key,
            title: archived.title,
            id: archived.id,
            seat,
            mine: archived.mine,
            total: archived.total,
            signed: archived.signed,
            via_linked: archived.via_linked,
            ended: resolution.as_ref().map(|r| r.headline()),
            concluded: resolution.as_ref().is_some_and(|r| r.concluded()),
        });
    }
    // Matches you PLAYED IN first, then the busiest, then stable by id.
    finished.sort_by(|a, b| {
        b.mine
            .cmp(&a.mine)
            .then_with(|| b.total.cmp(&a.total))
            .then_with(|| a.key.cmp(&b.key))
            .then_with(|| a.id.cmp(&b.id))
    });
    finished
}

/// Collect the viewer's live tables across the ship list.
///
/// `me` is the viewer's own identity; `linked` are the custodial identities a signed link record says
/// are the same human ([`identity_link::linked_actor_keys`]). A turn counts as the viewer's if it was
/// attributed to ANY of them — that union is the whole point of this page after a link, and it is
/// sound because every entry in `linked` was authorised by a signature from `me`'s own root key.
fn my_tables(
    state: &YouState,
    label: &str,
    me: &DreggIdentity,
    linked: &[DreggIdentity],
) -> Vec<MyTable> {
    let mut tables = Vec::new();
    for key in dreggnet_catalog::SHIPPED_KEYS {
        let owned_key = key.to_string();
        let actor = me.clone();
        let also = linked.to_vec();
        // ONE host job per offering: enumerate its live sessions and count this viewer's landed
        // turns off each log, on the host's own thread.
        let raw: Vec<RawSession> = state.catalog.run_offering(key, me, move |host| {
            host.session_ids(&owned_key)
                .into_iter()
                .map(|id| {
                    let (mine, total, signed, via_linked) = match host.move_log(&owned_key, &id) {
                        Some(log) => {
                            // One pass, no closure typing: a turn is the viewer's if it was
                            // attributed to their own identity OR to a provably linked platform one.
                            let (mut mine, mut signed, mut via_linked) = (0usize, 0usize, 0usize);
                            for logged in &log.moves {
                                let is_own = logged.actor == actor;
                                let is_linked = also.contains(&logged.actor);
                                if !is_own && !is_linked {
                                    continue;
                                }
                                mine += 1;
                                if logged.attribution.is_signed() {
                                    signed += 1;
                                }
                                if is_linked {
                                    via_linked += 1;
                                }
                            }
                            (mine, log.moves.len(), signed, via_linked)
                        }
                        None => (0, 0, 0, 0),
                    };
                    RawSession {
                        id: id.0,
                        mine,
                        total,
                        signed,
                        via_linked,
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
                via_linked: session.via_linked,
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

    // ⚑ THE LINK JOIN. For a CLAIMED viewer, `me.0` is their root public key, so the shared link
    // store can name the platform identities their own key signed a claim for.
    //
    // Gated on the label being a mac-verified CLAIM label, not merely on `me.0` looking like a key:
    // an anonymous visitor's identity is `blake3(label)`, which is also 64 hex chars, so without this
    // gate every casual page view would pay a link-store file read to learn nothing. A non-claimed
    // viewer therefore does ZERO extra I/O and every line below behaves exactly as it did before the
    // link door existed. The list is loaded ONCE and both the rendering and the joins read it.
    let links = if crate::seed_identity::parse_claim_label(&label).is_some() {
        identity_link::linked_platforms_for_root(&me.0)
    } else {
        Vec::new()
    };
    let linked: Vec<DreggIdentity> = identity_link::actor_keys_of(&links, &me.0)
        .into_iter()
        .map(DreggIdentity)
        .collect();

    let tables = my_tables(&state, &label, &me, &linked);
    // The SAME two joins (seat + actor), over the games that are OVER. Read off the archive rather
    // than off the live session set, which is the only reason this panel can exist at all.
    let finished = my_finished_matches(&state, &label, &me, &linked);
    // The board is joined on labels this page can stand behind for the viewer: the established
    // cookie label, the derived actor hex a signed / claimed submitter records, and every custodial
    // key a signed link record binds to this viewer's root. All matched EXACTLY by
    // `runs_for_labels` — no prefix, no resolver widening.
    let mut board_labels = vec![label.clone(), me.0.clone()];
    board_labels.extend(linked.iter().map(|id| id.0.clone()));
    let runs = state.descent.runs_for_labels(&board_labels);
    // Which day is TODAY, so "did today go better than yesterday" can be answered rather than
    // implied. Read off the board itself; `None` (no day open) simply drops the comparison.
    let today = state.descent.today();

    let mut response = Html(you_page(
        &label,
        &me,
        &links,
        &tables,
        &finished,
        &runs,
        today.as_deref(),
    ))
    .into_response();
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
/* A panel that holds two lists (your days, then every run) needs the second-level heading the shared
   skin does not otherwise style inside a section. */
.you-sub{margin:1.1rem 0 .1rem;font-family:var(--mono);font-size:var(--t-micro);text-transform:uppercase;letter-spacing:.12em;color:rgba(237,220,180,.55)}
</style>"##;

/// The one-line "what this page is" plaque plus every panel.
#[allow(clippy::too_many_arguments)]
fn you_page(
    label: &str,
    me: &DreggIdentity,
    links: &[LinkedPlatform],
    tables: &[MyTable],
    finished: &[FinishedMatch],
    runs: &[BoardRun],
    today: Option<&str>,
) -> String {
    let body = format!(
        "<main class=\"session af-table you-page\">\
         <div class=\"page-head\"><p class=\"eyebrow\">Your own record</p><h1>You</h1>\
         <p class=\"deck\">Everything this server can honestly say is yours: the tables it is \
         holding open for you, the matches you have already finished, the runs the board has under \
         your name, and the receipts your own moves minted. Every link here goes to the page that \
         re-runs the thing rather than to a copy of its result.</p></div>\
         {identity}{accounts}{tables}{finished}{runs}{receipts}\
         <p class=\"prose\"><a class=\"backlink\" href=\"/offerings\">← All games</a></p>\
         </main>",
        identity = identity_panel(label, me),
        accounts = accounts_panel(label, links),
        tables = tables_panel(tables),
        finished = finished_panel(finished),
        runs = runs_panel(label, runs, today),
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
    //
    // ⚑ The claimed branch carries `/identity`'s OWN restart caveat rather than only the good news.
    // A reader who never visits `/identity` reads this page as their whole answer, and "costs you
    // nothing you cannot type back" on its own is the rosier half of a two-part truth — the typing
    // back is not hypothetical, an unpinned deployment makes it a routine event.
    let durability = if crate::seed_identity::parse_claim_label(label).is_some() {
        "<p class=\"prose\"><strong>How durable is this?</strong> Recoverable. This identity is a \
         public key derived from 24 words you wrote down, so clearing your cookies or moving to \
         another device costs you nothing you cannot type back — everything below is filed under \
         the key, not under this browser. Keep those words where you can find them, because typing \
         them back is not only for a new device: unless this deployment pins its identity key, \
         restarting the server re-rolls it, this browser's claim stops verifying, and you arrive as \
         a fresh anonymous visitor until you enter your 24 words again — never as somebody else. \
         What it still is <em>not</em>: a signature. Your moves are attributed to your key, not \
         signed by it, because neither this page nor the server holds the secret. A tool that holds \
         your phrase can sign as you; see <a href=\"/identity\">your identity</a>.</p>"
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

/// ⚑ **THE LINKED-ACCOUNTS PANEL — and the asymmetry, stated where the union is shown.**
///
/// This is the panel that makes the union visible, so it is also the panel that must not let a player
/// walk away believing the link gave them something it did not. Three things are said in every state:
///
/// * the two keys are **still two keys** — nothing was imported or re-keyed;
/// * a platform key is **custodial**: the operator's `bot_secret` derives it, before and after the
///   link, and the link cannot change that;
/// * what the link *is* — the board ranks you once, and this page counts both sides.
///
/// Rendering the custody sentence off [`LinkedPlatform::operator_derivable`] rather than off a string
/// match means a future platform cannot be added without answering the custody question.
fn accounts_panel(label: &str, links: &[LinkedPlatform]) -> String {
    let claimed = crate::seed_identity::parse_claim_label(label).is_some();
    if links.is_empty() {
        // Two genuinely different reasons; saying the wrong one is the staleness trap this page has
        // already been bitten by twice (see the branched paragraphs above).
        let why = if claimed {
            "<p class=\"you-empty\">Your Discord and Telegram selves are, right now, <strong>a \
             different player from this one</strong> — a different key, a different history, and a \
             separate row on the same board. That is not a bug in the boards; nothing has ever \
             connected them. <a href=\"/identity/link\">Prove they are the same human</a> and this \
             page starts counting both, and the Descent board ranks you once instead of twice.</p>"
        } else {
            "<p class=\"you-empty\">Linking needs an identity to link <em>to</em>: a key your own 24 \
             words derive. This browser has a cookie label instead, which nothing can sign a claim \
             with. <a href=\"/identity\">Claim a recoverable identity</a> first; the link door is \
             one step after it.</p>"
        };
        return format!(
            "<section class=\"deos-section tag-muted\"><h2>Your other accounts</h2>\
             <p class=\"you-empty\"><strong>No other account is linked to this one.</strong></p>\
             {why}</section>"
        );
    }
    let rows: String = links
        .iter()
        .map(|link| {
            let is_web = link.platform == WEB_PLATFORM;
            let what = if is_web {
                "This surface — the identity your 24 words derive.".to_string()
            } else {
                format!("account {}", esc(&link.platform_uid))
            };
            let custody = if link.operator_derivable {
                "<strong>Custodial.</strong> The bot's operator can derive this key from their own \
                 secret and act as you there — that was true before you linked and it is true now. \
                 Linking joined the records, not the custody."
            } else {
                "<strong>Self-held.</strong> Only your 24 words reproduce this key; nobody else can, \
                 us included."
            };
            format!(
                "<div class=\"you-row\"><p class=\"what\">{platform}</p>\
                 <p class=\"meta\">{what} · key {key}…</p>\
                 <p class=\"said\">{custody}</p></div>",
                platform = esc(&link.platform),
                what = what,
                key = esc(&link.custodial_pubkey_hex.chars().take(16).collect::<String>()),
                custody = custody,
            )
        })
        .collect();
    let others = links.iter().filter(|l| l.operator_derivable).count();
    format!(
        "<section class=\"deos-section tag-accent\"><h2>Your other accounts</h2>\
         <p class=\"prose\">{others} platform account{s} {is} proven to be this same human, so \
         everything below counts both sides and the Descent board ranks you <em>once</em> rather \
         than as strangers who happen to play alike.</p>\
         <div class=\"you-rows\">{rows}</div>\
         <p class=\"you-empty\"><strong>What the link did not do.</strong> It did not merge the \
         keys, and it did not make your platform key yours. Each account still signs with its own \
         key under its own custody — the difference is real, it is printed on each row above, and \
         joining the records is not allowed to hide it. What changed is the <em>view</em>: this page \
         and the board now know the accounts are one person. \
         <a href=\"/identity/link\">Link another account</a>.</p></section>",
        others = others,
        s = if others == 1 { "" } else { "s" },
        is = if others == 1 { "is" } else { "are" },
        rows = rows,
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
    // The union is NAMED per table rather than folded into one number: a turn that landed under a
    // linked platform's custodial key is still that key's turn, and saying so is the difference
    // between joining two records and pretending there was only ever one.
    if table.via_linked > 0 {
        parts.push(format!(
            "{} of them landed on a linked account (custodial key)",
            table.via_linked
        ));
    }
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
             opened a table yet — or the one you opened has since ENDED, in which case it is in \
             <em>Matches you have finished</em> below rather than gone. Nothing has been lost that \
             this page is hiding.</p>\
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
                 {watch}\
                 <p class=\"meta\"><a href=\"{verify}\" rel=\"nofollow\">Replay-verify this \
                 chain</a></p>\
                 </div>",
                over = if table.resolved.is_some() {
                    " is-over"
                } else {
                    ""
                },
                // ⚑ THE LINK A PLAYER CAME HERE FOR. The watch route has always worked; it was
                // reachable only from the mint's one-shot lobby page, so somebody mid-match had
                // nothing to send a friend and reported that web spectating did not exist. No
                // secret rides it (the id is already printed above), it is `None` on an ad-hoc
                // session, and it stays useful after the ending — a resolved table's final position
                // is exactly what the spectator view shows.
                watch = table
                    .watch_href()
                    .map(|href| format!(
                        "<p class=\"meta\"><a href=\"{href}\">{verb} — a link that holds no \
                         seat</a></p>",
                        href = esc(&href),
                        verb = if table.resolved.is_some() {
                            "Share the final position"
                        } else {
                            "Let someone watch this table"
                        },
                    ))
                    .unwrap_or_default(),
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
         it, or because a move of yours landed in it. Closing the tab never ended any of them, and \
         when one does end it moves to <em>Matches you have finished</em> rather than disappearing.\
         </p>\
         <div class=\"you-rows\">{rows}</div></section>",
        count = tables.len(),
        s = if tables.len() == 1 { "" } else { "s" },
        is = if tables.len() == 1 { "is" } else { "are" },
        rows = rows,
    )
}

/// ⚑ **THE FINISHED MATCHES PANEL** — the history this page had to cut on the day it shipped.
///
/// Every row points at the route that RE-EXECUTES the match rather than at a stored verdict, which is
/// the same discipline the Descent panel below runs on and the reason the claim "a finished game can
/// be replayed by anyone" is now true for two of the three games instead of one.
fn finished_panel(finished: &[FinishedMatch]) -> String {
    if finished.is_empty() {
        return "<section class=\"deos-section tag-muted\"><h2>Matches you have finished</h2>\
                <p class=\"you-empty\"><strong>You have not finished a match here yet.</strong> A \
                table lands in this panel when it ends — played out, resigned, or forfeited on the \
                clock — and it stays: the moves are kept, so the finished game can be re-executed \
                from them by anyone you send the link to.</p>\
                <p class=\"you-empty\">A game still in play is in the panel above, not here. \
                Nothing has been thrown away that this panel is hiding.</p></section>"
            .to_string();
    }
    let rows: String = finished
        .iter()
        .map(|game| {
            let mut parts: Vec<String> = Vec::new();
            if let Some(seat) = game.seat {
                parts.push(format!("seat {}", seat.label()));
            }
            parts.push(format!("session {}", game.id));
            parts.push(format!(
                "{mine} of {total} landed turn{s} yours",
                mine = game.mine,
                total = game.total,
                s = if game.total == 1 { "" } else { "s" },
            ));
            parts.push(if game.signed > 0 {
                format!("{} signed", game.signed)
            } else {
                "asserted attribution".to_string()
            });
            if game.via_linked > 0 {
                parts.push(format!(
                    "{} of them landed on a linked account (custodial key)",
                    game.via_linked
                ));
            }
            // The ending, in the lobby's own words, and NEVER upgraded into a result. A match that
            // played itself out says so; a forfeit says it is not a proven win.
            let said = match game.ended.as_deref() {
                Some(headline) if game.concluded => format!(
                    "<p class=\"said\">This match is over — {}. Neither seat is owed a move, so the \
                     final board is the result; this lobby does not name a winner, the game's own \
                     rules do.</p>",
                    esc(headline)
                ),
                Some(headline) => format!(
                    "<p class=\"said\">This match ended — {}. No executor turn backs that: it is \
                     the lobby's record of somebody stopping, not a proven win.</p>",
                    esc(headline)
                ),
                // Honest about the one thing the archive alone cannot say.
                None => "<p class=\"said\">This match is over and its moves are kept, but this \
                         server no longer holds a record of <em>how</em> it ended — the ending was \
                         not persisted (or predates the record). The moves still re-execute.</p>"
                    .to_string(),
            };
            format!(
                "<div class=\"you-row is-over\">\
                 <p class=\"what\">{title}</p>\
                 <a class=\"go\" href=\"{verify}\" rel=\"nofollow\">Replay this match →</a>\
                 <p class=\"meta\">{meta}</p>\
                 {said}\
                 </div>",
                title = esc(&game.title),
                verify = esc(&game.verify_href()),
                meta = esc(&parts.join(" · ")),
                said = said,
            )
        })
        .collect();
    format!(
        "<section class=\"deos-section tag-accent\"><h2>Matches you have finished</h2>\
         <p class=\"prose\">{count} finished match{es} {is} yours. Closing a table no longer throws \
         the game away: its recorded moves are kept, and <strong>Replay this match</strong> \
         re-executes them through the same rules that admitted them in the first place — a real \
         re-run taken when you open it, not a verdict somebody wrote down. Send that link to anyone; \
         it proves itself to them the same way.</p>\
         <div class=\"you-rows\">{rows}</div>\
         <p class=\"you-empty\">What a replay does <em>not</em> settle: who won. It shows that these \
         moves were legal and landed in this order. A win is whatever the game's own rules made of \
         the final board — that is on the board, not in this list.</p></section>",
        count = finished.len(),
        es = if finished.len() == 1 { "" } else { "es" },
        is = if finished.len() == 1 { "is" } else { "are" },
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

/// ⚑ **YOUR DAYS, SIDE BY SIDE** — one line per day the board has a run of yours on, newest first,
/// each carrying the best score you reached that day and how that compares with the day before.
///
/// This is the half of "a daily game" that was stated and not felt. The board ranks you against other
/// people; nothing anywhere answered *did today go better than yesterday*, because a run had no single
/// number to compare. It has one now ([`crate::descent_card::RunScore`]) — and the comparison here is
/// arithmetic on it, never a rank: no ordering rule is applied to anybody, only your own days
/// subtracted from each other.
struct DayLine {
    day_key: String,
    is_today: bool,
    /// The best score you reached that day, and its `banked/total` form. `None` when every run of
    /// yours that day was on a lane that has no score (see [`BoardRun::score`]).
    best_score: Option<u64>,
    best_cell: Option<String>,
    /// The deepest floor you reached that day, and how many runs the board holds.
    best_depth: u64,
    runs: usize,
    /// How many of them provably finished (the hoard on the procgen board, a crown on the native lane).
    finished: usize,
    /// The best score of the NEXT line (the day before this one), for the delta. Filled after sorting.
    previous_score: Option<u64>,
}

impl DayLine {
    /// The comparison sentence — the whole reason this block exists. It is stated only when both days
    /// really have a score, because "you improved by 5" against a day with nothing to compare is the
    /// kind of confident nonsense a daily game loses people over.
    fn against_yesterday(&self) -> Option<String> {
        let (now, before) = (self.best_score?, self.previous_score?);
        Some(match now.cmp(&before) {
            std::cmp::Ordering::Greater => format!(
                "up {} on your previous day ({before})",
                now.saturating_sub(before)
            ),
            std::cmp::Ordering::Less => format!(
                "down {} on your previous day ({before})",
                before.saturating_sub(now)
            ),
            std::cmp::Ordering::Equal => format!("level with your previous day ({before})"),
        })
    }
}

/// Fold the viewer's runs into one line per day, newest-looking first with TODAY pinned to the top,
/// and wire each line's `previous_score` to the day below it.
fn day_lines(runs: &[BoardRun], today: Option<&str>) -> Vec<DayLine> {
    let mut lines: Vec<DayLine> = Vec::new();
    for run in runs {
        // The INDEX, not a `&mut` from `iter_mut().find(…)`: that borrow would still be live in the
        // absent arm where the push happens.
        let index = match lines.iter().position(|line| line.day_key == run.day_key) {
            Some(index) => index,
            None => {
                lines.push(DayLine {
                    day_key: run.day_key.clone(),
                    is_today: today == Some(run.day_key.as_str()),
                    best_score: None,
                    best_cell: None,
                    best_depth: 0,
                    runs: 0,
                    finished: 0,
                    previous_score: None,
                });
                lines.len() - 1
            }
        };
        let slot = &mut lines[index];
        slot.runs += 1;
        if run.finished && run.verified {
            slot.finished += 1;
        }
        slot.best_depth = slot.best_depth.max(run.depth);
        // The BEST score of the day is the one that represents it — same rule the board uses to pick
        // a human's row, applied to a person's own day.
        if let Some(value) = run.score_value() {
            if slot.best_score.is_none_or(|best| value > best) {
                slot.best_score = Some(value);
                slot.best_cell = run.score_cell();
            }
        }
    }
    // Day keys are opaque strings, so the honest ordering is: TODAY first (the board itself told us
    // which one that is), then descending by key — which for this deployment's `d{utc}-…` keys is
    // newest-first, and for anything else is at least stable and never claims a false chronology.
    lines.sort_by(|a, b| {
        b.is_today
            .cmp(&a.is_today)
            .then_with(|| b.day_key.cmp(&a.day_key))
    });
    for index in 0..lines.len() {
        lines[index].previous_score = lines.get(index + 1).and_then(|next| next.best_score);
    }
    lines
}

/// The day-by-day block. Absent (empty string) when there is only one day to show, because a
/// comparison table with one row is a comparison of nothing.
fn days_block(lines: &[DayLine]) -> String {
    if lines.len() < 2 {
        return String::new();
    }
    let rows: String = lines
        .iter()
        .map(|line| {
            let mut parts = vec![
                format!("{} run{}", line.runs, if line.runs == 1 { "" } else { "s" }),
                format!("deepest floor {}", line.best_depth),
            ];
            if line.finished > 0 {
                parts.push(format!("{} finished", line.finished));
            }
            match (&line.best_cell, line.against_yesterday()) {
                (Some(cell), Some(delta)) => {
                    parts.push(format!("score {cell}"));
                    parts.push(delta);
                }
                (Some(cell), None) => parts.push(format!("score {cell}")),
                // A day whose only runs were on the procgen lane genuinely has no score; say which.
                (None, _) => parts.push("no score on this lane".to_string()),
            }
            format!(
                "<div class=\"you-row{today}\"><p class=\"what\">{when}</p>\
                 <a class=\"go\" href=\"/descent/leaderboard?day={day}\">That day's board →</a>\
                 <p class=\"meta\">{meta}</p></div>",
                today = if line.is_today { "" } else { " is-over" },
                when = if line.is_today {
                    "Today".to_string()
                } else {
                    format!("Day {}", esc(&line.day_key))
                },
                day = esc(&line.day_key),
                meta = esc(&parts.join(" · ")),
            )
        })
        .collect();
    format!(
        "<h3 class=\"you-sub\">Your days</h3>\
         <p class=\"prose\">Your own record, day by day — newest first. <span \
         class=\"mono\">score</span> is the relic depth you carried out: every banked relic counts \
         the floor it was minted on, read off that day's own drawn map. It is a <em>read</em> over \
         what your run already committed, not a ranking rule and not a rating; the only thing \
         compared here is you against yourself.</p>\
         <div class=\"you-rows\">{rows}</div>",
        rows = rows,
    )
}

fn runs_panel(label: &str, runs: &[BoardRun], today: Option<&str>) -> String {
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
            // THE RUN'S ONE NUMBER, where the run is. A lane with no score prints nothing rather than
            // a zero that would read as "banked nothing".
            if let Some(cell) = run.score_cell() {
                parts.push(format!("score {cell}"));
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
         {days}\
         <h3 class=\"you-sub\">Every run</h3>\
         <div class=\"you-rows\">{rows}</div>{local}</section>",
        count = runs.len(),
        s = if runs.len() == 1 { "" } else { "s" },
        y = if runs.len() == 1 { "ies" } else { "y" },
        days = days_block(&day_lines(runs, today)),
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
        let runs = runs_panel("visitor-abc", &[], None);
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
        // The finished-match panel gets the same treatment, and its empty state has one extra job:
        // it must say that a match which ENDED is kept rather than thrown away, because "nothing
        // here" is exactly what a player would otherwise read as "you lost your history".
        let finished = finished_panel(&[]);
        assert!(
            finished.contains("You have not finished a match here yet"),
            "{finished}"
        );
        assert!(
            finished.contains("the moves are kept"),
            "the empty finished panel must promise the thing that changed: {finished}"
        );
        // No panel may render as an unexplained blank.
        for panel in [&tables, &runs, &receipts, &finished] {
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
            // A refusal must not assemble the match HISTORY either — it names which tables this
            // person sat at, which is exactly as personal as the live list.
            "Matches you have finished",
            // The linked-accounts panel names OTHER platform accounts of this human — the most
            // personal thing on the page, so a refusal must not assemble it either.
            "Your other accounts",
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
        // ⚑ …and it carries `/identity`'s own restart caveat, so a reader who only ever visits
        // `/you` does not get the rosier half of the truth. "Nothing you cannot type back" is true;
        // "and here is when you will have to" is the part that was missing.
        assert!(
            panel.contains("restarting the server re-rolls it"),
            "the claimed branch must carry the restart caveat: {panel}"
        );
        assert!(
            panel.contains("never as somebody else"),
            "the caveat must also say what a restart is NOT: {panel}"
        );
        // Still honest about the one thing a claim does NOT buy on this surface.
        assert!(panel.contains("not signed by it"), "{panel}");
        assert!(
            panel.contains("neither this page nor the server holds"),
            "{panel}"
        );
        // The credential (the mac'd label) still never reaches the page.
        assert!(!panel.contains(&label), "{panel}");
    }

    /// ⚑ The linked-accounts panel states the CUSTODY ASYMMETRY on every row, and never sells the
    /// link as having made the platform key the player's. The custody sentence is driven off
    /// `operator_derivable`, so a new platform cannot be added without answering that question.
    #[test]
    fn the_accounts_panel_never_launders_the_custodial_asymmetry() {
        let links = vec![
            LinkedPlatform {
                platform: WEB_PLATFORM.to_string(),
                platform_uid: "ab".repeat(32),
                custodial_pubkey_hex: "ab".repeat(32),
                verified_at: 1,
                operator_derivable: false,
            },
            LinkedPlatform {
                platform: "discord".to_string(),
                platform_uid: "6913902526".to_string(),
                custodial_pubkey_hex: "cd".repeat(32),
                verified_at: 2,
                operator_derivable: true,
            },
        ];
        let panel = accounts_panel("visitor-abc", &links);
        assert!(panel.contains("Custodial."), "{panel}");
        assert!(panel.contains("Self-held."), "{panel}");
        assert!(
            panel.contains("true before you linked and it is true now"),
            "the link must not be sold as changing custody: {panel}"
        );
        assert!(
            panel.contains("did not merge the keys"),
            "the no-merge statement is missing: {panel}"
        );
        assert!(
            panel.contains("ranks you <em>once</em>"),
            "the panel must say what the link IS for: {panel}"
        );
        // ONE platform is counted, not two — the web self-row is this surface, not another account.
        assert!(panel.contains("1 platform account is proven"), "{panel}");
    }

    /// The empty accounts panel branches on WHY, because the two reasons are genuinely different and
    /// telling a claimed player to go claim an identity would be the staleness trap again.
    #[test]
    fn the_empty_accounts_panel_names_the_right_missing_step() {
        let unclaimed = accounts_panel("visitor-abc", &[]);
        assert!(unclaimed.contains("/identity\""), "{unclaimed}");
        assert!(
            !unclaimed.contains("/identity/link"),
            "a cookie label cannot sign a link claim, so do not offer the link door: {unclaimed}"
        );

        let pubkey_hex =
            crate::seed_identity::derive_pubkey_hex(&dregg_sdk::mnemonic::generate_mnemonic())
                .expect("a generated phrase derives");
        let claimed = accounts_panel(&crate::seed_identity::claim_label(&pubkey_hex), &[]);
        assert!(claimed.contains("/identity/link"), "{claimed}");
        assert!(
            claimed.contains("a different player from this one"),
            "an unlinked claimed player must be told the split is REAL: {claimed}"
        );
    }

    /// A unioned turn count NAMES the linked side rather than folding two custodies into one number.
    #[test]
    fn a_table_meta_names_turns_that_landed_on_a_linked_account() {
        let table = MyTable {
            key: "descent".into(),
            title: "The Descent".into(),
            id: "s1".into(),
            seat: None,
            mine: 5,
            total: 9,
            signed: 3,
            via_linked: 3,
            resolved: None,
            verified: Some((true, 9, String::new())),
        };
        let meta = table_meta(&table);
        assert!(
            meta.contains("3 of them landed on a linked account"),
            "{meta}"
        );
        assert!(meta.contains("custodial key"), "{meta}");
        // With nothing linked the line is byte-identical to before.
        let alone = MyTable {
            via_linked: 0,
            ..table
        };
        assert!(!table_meta(&alone).contains("linked account"));
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

    fn finished_fixture(id: &str, ended: Option<&str>, concluded: bool) -> FinishedMatch {
        FinishedMatch {
            key: "automatafl".into(),
            title: "Automatafl".into(),
            id: id.into(),
            seat: Some(SeatSlot::A),
            mine: 4,
            total: 7,
            signed: 0,
            via_linked: 0,
            ended: ended.map(str::to_string),
            concluded,
        }
    }

    /// ⚑ A FINISHED MATCH ROW POINTS AT THE REPLAY, and says how the match ended in the lobby's own
    /// register — a match that played itself out must not be described with the walked-away words, and
    /// a forfeit must still refuse to be called a proven win.
    #[test]
    fn a_finished_match_row_links_at_the_replay_and_never_overstates_the_ending() {
        let played_out = finished_fixture(
            "af1-played-out",
            Some("this table played itself out — neither seat is owed a move"),
            true,
        );
        let panel = finished_panel(&[played_out]);
        assert!(
            panel.contains("/offerings/automatafl/session/af1-played-out/verify"),
            "the row must point at the route that RE-EXECUTES the match: {panel}"
        );
        assert!(panel.contains("Replay this match"), "{panel}");
        assert!(
            panel.contains("seat A") && panel.contains("4 of 7 landed turns yours"),
            "the seat and actor joins must survive into the finished list: {panel}"
        );
        assert!(
            panel.contains("this lobby does not name a winner"),
            "a concluded match must not be sold as a decided one: {panel}"
        );
        assert!(
            !panel.contains("somebody stopping"),
            "the walked-away sentence leaked onto a played-out match: {panel}"
        );

        // NON-VACUOUS: a forfeit gets the OTHER sentence, and keeps its disclaimer.
        let forfeited = finished_panel(&[finished_fixture(
            "af1-forfeit",
            Some("seat B let the clock run out"),
            false,
        )]);
        assert!(forfeited.contains("somebody stopping"), "{forfeited}");
        assert!(forfeited.contains("not a proven win"), "{forfeited}");
        assert!(!forfeited.contains("does not name a winner"), "{forfeited}");

        // …and a match whose ENDING was never persisted says exactly that, rather than inventing one.
        let unknown = finished_panel(&[finished_fixture("af1-unknown-end", None, false)]);
        assert!(
            unknown.contains("no longer holds a record of"),
            "an unknown ending must be admitted: {unknown}"
        );
        assert!(
            unknown.contains("moves still re-execute"),
            "…while still promising the thing that IS true: {unknown}"
        );
    }

    fn board_run(day: &str, turns: usize, depth: u64, score: Option<u64>) -> BoardRun {
        BoardRun {
            run_id: format!("{day}-{turns}"),
            day_key: day.into(),
            label: "web:me".into(),
            native: score.is_some(),
            path: format!("/descent/native/run/{day}-{turns}"),
            turns,
            depth,
            verified: true,
            finished: true,
            relics: 2,
            score: score.map(|banked_depth| crate::descent_card::RunScore {
                banked_depth,
                shaft_depth: 17,
                frozen_depth: 0,
                deepest: depth,
                floors: 4,
                light_left: 3,
                light_breath: 30,
                crowned: true,
                banked_count: 2,
            }),
        }
    }

    /// ⚑ **TODAY BESIDE YESTERDAY.** The daily hook was stated and not felt because nothing compared
    /// a player with their own past. This pins the comparison: today is first, the delta against the
    /// previous day is stated in words, and a day whose runs carry no score is never given one.
    #[test]
    fn your_days_are_ordered_with_today_first_and_compared_against_the_day_before() {
        let runs = vec![
            board_run("d100-off", 20, 3, Some(7)),
            board_run("d101-off", 25, 4, Some(12)),
            board_run("d101-off", 31, 4, Some(9)), // the SAME day, a worse haul
        ];
        let lines = day_lines(&runs, Some("d101-off"));
        assert_eq!(lines.len(), 2, "one line per day, not per run");
        assert!(
            lines[0].is_today,
            "today must read first: {:?}",
            lines[0].day_key
        );
        assert_eq!(lines[0].day_key, "d101-off");
        assert_eq!(lines[0].runs, 2);
        assert_eq!(
            lines[0].best_score,
            Some(12),
            "the day is represented by your BEST haul on it, not your last"
        );
        assert_eq!(lines[0].previous_score, Some(7));
        let delta = lines[0]
            .against_yesterday()
            .expect("both days have a score, so the comparison is honest");
        assert!(delta.contains("up 5"), "{delta}");

        // The older day has nothing before it, so it makes NO claim.
        assert!(lines[1].against_yesterday().is_none());

        let block = days_block(&lines);
        assert!(block.contains("Today"), "{block}");
        assert!(block.contains("Day d100-off"), "{block}");
        assert!(block.contains("score 12/17"), "{block}");
        assert!(block.contains("up 5 on your previous day"), "{block}");
        assert!(
            block.contains("not a ranking rule"),
            "the block must say what the score is NOT: {block}"
        );

        // A SCORELESS lane must not be compared as a zero — that would tell a procgen player they
        // went backwards on a day they never played the scored lane.
        let procgen_only = vec![
            board_run("d102-off", 9, 2, None),
            board_run("d103-off", 8, 3, None),
        ];
        let bare = day_lines(&procgen_only, Some("d103-off"));
        assert!(bare.iter().all(|line| line.best_score.is_none()));
        assert!(bare.iter().all(|line| line.against_yesterday().is_none()));
        let bare_block = days_block(&bare);
        assert!(bare_block.contains("no score on this lane"), "{bare_block}");
        assert!(!bare_block.contains("down "), "{bare_block}");

        // One day is not a comparison, so the block does not pretend to be one.
        assert!(days_block(&day_lines(&runs[..1], Some("d100-off"))).is_empty());
    }

    /// A run's own row carries the score, and a scoreless lane prints no score rather than a `0`
    /// that would read as "you banked nothing".
    #[test]
    fn a_run_row_shows_its_score_only_when_its_lane_has_one() {
        let scored = runs_panel(
            "web:me",
            &[board_run("d1-off", 25, 4, Some(11))],
            Some("d1-off"),
        );
        assert!(scored.contains("score 11/17"), "{scored}");
        let unscored = runs_panel(
            "web:me",
            &[board_run("d1-off", 25, 4, None)],
            Some("d1-off"),
        );
        assert!(
            !unscored.contains("score "),
            "a lane with no score must print none: {unscored}"
        );
    }
}
