//! # The Descent's own door — one press, and the run behind it is YOURS.
//!
//! ## The wound this closes
//!
//! Every server-side play CTA on the product pointed at ONE fixed session id,
//! `/offerings/descent/session/descent-web`: the catalog card's *"Play →"*, `/descent/play`'s
//! *"Start today's run →"*, its `<noscript>` *"play it here"*, and the engine grid's *"Play now"*.
//! That id is the catalog's generic demo-session convention (`{key}-web`), and it is the right
//! convention for a council or a market — a shared table by nature, holding nothing private and
//! binding nobody.
//!
//! The native Descent is not a table. It is **single-owner by construction**: the first move that
//! LANDS binds `NativeDescentSession::actor`, and from then on every other identity is refused with
//! [`dreggnet_offerings::refusal::belongs_to_another_player`]. So the first visitor who took a turn
//! in `descent-web` became the permanent owner of the product's entire front door, and every
//! visitor after them arrived at a board they were not allowed to touch, with nothing on the page
//! offering them a run of their own. *"Start today's run"* could not start a run.
//!
//! The bug was never the ownership check. That check is what makes a run mean anything. The bug is
//! that a **shared entry point was claimable at all** — a CTA pointing at one session for everyone,
//! aimed at a game whose sessions belong to one person.
//!
//! ## The shape, which is automatafl's and the tug's
//!
//! [`crate::table_door`] already solved this for the two-player games: the catalog card links a
//! DOOR, and the door opens a session per player. This is that shape for a game played alone, so it
//! needs neither seats nor invites nor a spectator lock — just an address that means *my run*:
//!
//! * `GET /descent/play/run` — 303 to the run this browser owns today, opening it if it is the
//!   first press and RESUMING it if it is not.
//!
//! ## Why a redirect and not a mint button
//!
//! `table_door`'s mint is a POST because pressing it MINTS a fresh table, and a side-effecting GET
//! would let a link prefetcher open tables nobody asked for. This route has no such side effect to
//! protect: the id it sends you to is **derived**, so the same browser on the same day is sent to
//! the same run however many times it is pressed, and the world is deployed by the ordinary session
//! route on arrival exactly as it is for any hand-typed id. Pressing the CTA twice resumes; it does
//! not open a second run.
//!
//! That also keeps the CTA one press wide. `/descent/play` is already the Descent's landing page
//! (rules, engine choice, hero); putting a second landing page between its primary button and the
//! board would re-introduce the middle click [`crate::descent_play`]'s primary CTA exists to remove.
//!
//! ## The derivation, and what it is secret against
//!
//! `id = dr1-{serial}-{96 bits of blake3_keyed(K, "…v1" ‖ label ‖ day ‖ serial)}`, under a
//! server-only key resolved by the same ladder every other server key here uses
//! ([`crate::table_seats::resolve_process_key`]: an operator pin, then a `0600` file under
//! `DREGGNET_WEB_SESSION_DIR`, then process-random).
//!
//! Keyed, not a bare hash, and the reason is a real reader rather than a threat-model reflex: the
//! browser label of a player who has CLAIMED an identity ([`crate::seed_identity`]) contains their
//! public key, which is printed on public boards. An unkeyed derivation would therefore let anyone
//! compute a claimed player's run address, read the whole run (this surface discloses a hosted run
//! to anyone holding its link, and says so), and — before that player's first move — take the run
//! by moving in it first. Under the key, nobody can derive anybody's address but their own.
//!
//! ⚠ **The fail-closed cost, stated:** on a deployment with no `DREGGNET_WEB_SESSION_DIR` the key
//! is process-random, so a restart changes every derived address and the door stops being the way
//! back to a run already in progress. The run is not lost — it is still live, still owned, and still
//! listed with a resume link on `/you`, which joins live sessions to the viewer by the logged actor
//! rather than by any address. Setting the session dir (which a real deployment sets anyway, for
//! durable sessions) removes the condition.
//!
//! ⚠ **And two things the address does NOT do**, said here rather than left to be discovered:
//!
//! * **It is not a secret that keeps a run private once it is shared.** A hosted Descent discloses
//!   itself to whoever holds its link, and the session page says so in those words. The key stops
//!   somebody DERIVING your address; it does nothing about one you paste. That is why [`run_note`]
//!   states a property of the board rather than a claim about whoever is reading it.
//! * **It does not follow a player who claims an identity mid-run.** Claiming a phrase rewrites
//!   `dregg_user` (`seed_identity`), so the label changes, so the derived address changes and the
//!   run in progress falls out of reach of the door. That is the pre-existing consequence of
//!   changing names mid-play on a surface whose actor IS the label — the same discontinuity the
//!   post-first-move identity offer already warns about — and this door neither causes it nor
//!   repairs it.
//!
//! ## The serial, and the one policy this door asserts
//!
//! A Descent run ENDS: `fate != 0` and the offering offers no further action. A door that always
//! resolved to serial 0 would hand a player who finished a dead board and no way past it, which is
//! the same dead end one day later. So the door walks serials from 0 and stops at the first run
//! that is not over — resume while you are playing, a fresh run once you are not.
//!
//! The walk is bounded at [`RUNS_PER_DAY`], and that bound is the door's one policy: it is what
//! keeps one browser from opening unbounded server-side worlds by holding down a link. When it is
//! reached the door says so in words rather than redirecting into a finished board, and names the
//! in-tab engine, which runs on the reader's own machine and is bounded by nothing here.

use std::sync::Arc;

use axum::Router;
use axum::extract::{Query, State};
use axum::http::{HeaderMap, StatusCode, header};
use axum::response::{Html, IntoResponse, Response};
use axum::routing::get;
use dreggnet_offerings::{DreggIdentity, SessionId};

use crate::web_identity_http::web_user_established;
use crate::{CatalogState, WebQuery, document, esc, hex_bytes};

/// The catalog key this door opens.
pub const KEY: &str = "descent";

/// **The address every server-side Descent play CTA points at.** One press from the CTA to a board
/// the presser owns; named once so the catalog card, the play page's primary button, its
/// `<noscript>` fallback and the engine grid cannot drift into pointing at different front doors.
pub const DESCENT_RUN_PATH: &str = "/descent/play/run";

/// The prefix a door-opened run id wears. An id without it is an ad-hoc session on the catalog's
/// ordinary rules ([`DEMO_RUN`] included) and is not anybody's door.
pub const RUN_PREFIX: &str = "dr1-";

/// **The named demo run.** The old front door, kept and demoted: nothing links to it as a place to
/// play, and its page now says what it is ([`run_note`]).
pub const DEMO_RUN: &str = "descent-web";

/// **How many hosted runs one browser may open in a day.** The door's one policy, and the reason a
/// derived address can safely be reached by a plain link: without a ceiling, one browser pressing
/// the CTA again after each finished run would open server-side worlds without end.
///
/// It bounds the HOSTED engine only. The in-tab engine (`/descent/play?engine=browser`) runs on the
/// reader's own machine and is bounded by nothing here, which is what [`daily_limit_body`] says.
pub const RUNS_PER_DAY: u32 = 12;

/// The key every run address is derived under. Never served, never logged.
fn run_key() -> &'static [u8; 32] {
    static KEY_CELL: std::sync::OnceLock<[u8; 32]> = std::sync::OnceLock::new();
    KEY_CELL.get_or_init(|| {
        crate::table_seats::resolve_process_key(
            "DREGGNET_WEB_DESCENT_RUN_KEY",
            "descent-run-key.bin",
            "the addresses of runs already in progress",
        )
    })
}

/// **The address of `label`'s `serial`-th Descent run on `day`.** Deterministic, so the door is a
/// navigation rather than a mint; keyed, so it is nobody else's to derive. The `\0` separators keep
/// a long label and a short day from colliding with a short label and a long day.
pub fn run_id(label: &str, day: &str, serial: u32) -> String {
    let mut input = Vec::with_capacity(label.len() + day.len() + 32);
    input.extend_from_slice(b"dregg.descent.run.v1\0");
    input.extend_from_slice(label.as_bytes());
    input.push(0);
    input.extend_from_slice(day.as_bytes());
    input.push(0);
    input.extend_from_slice(&serial.to_le_bytes());
    let tag = blake3::keyed_hash(run_key(), &input);
    format!("{RUN_PREFIX}{serial}-{}", hex_bytes(&tag.as_bytes()[..12]))
}

/// Whether `id` names a run this door opened.
pub fn is_own_run(id: &str) -> bool {
    id.starts_with(RUN_PREFIX)
}

/// The play surface a run id lives at.
pub fn run_link(id: &str) -> String {
    format!("/offerings/{KEY}/session/{id}")
}

/// **Assemble the Descent's door.** Additive: `/descent/play/run` overlaps neither
/// [`crate::descent_router`]'s board surface (`/descent`, `/descent/run/{id}`) nor
/// [`crate::descent_play::descent_play_router`]'s shell and static assets.
///
/// The visitor-cookie bootstrap is layered on deliberately. The door refuses to open a run for a
/// caller whose name is not the durable `dregg_user` cookie (see [`get_open_run`]), and a browser
/// arriving here for the very first time has no cookie yet — the same middleware the catalog routes
/// carry mints it on this request, so a stranger's first press works and the run they open is one
/// they can come back to.
pub fn descent_door_router(state: Arc<CatalogState>) -> Router {
    Router::new()
        .route(DESCENT_RUN_PATH, get(get_open_run))
        .layer(axum::middleware::from_fn(
            crate::web_identity_http::bootstrap_visitor_identity,
        ))
        .with_state(state)
}

/// `GET /descent/play/run` — 303 to the run this browser owns today.
async fn get_open_run(
    State(state): State<Arc<CatalogState>>,
    headers: HeaderMap,
    Query(query): Query<WebQuery>,
) -> Response {
    let (label, established) = web_user_established(&headers, &query);
    // ⚑ ESTABLISHED ONLY, and this is the flood backstop rather than an identity ritual. The
    // derived address is a pure function of the label, so an attacker-chosen `?user=` would let one
    // client walk `?user=1,2,…,N` and open `RUNS_PER_DAY` hosted worlds per invented name. A durable
    // cookie is the one label this server minted, and it is what the ceiling is counted against.
    if !established {
        return (
            StatusCode::FORBIDDEN,
            Html(page(NO_IDENTITY_TITLE, no_identity_body())),
        )
            .into_response();
    }
    let day = crate::descent::todays_day();
    let viewer = crate::seed_identity::resolve_identity(&label);
    let Some(id) = current_run(&state, &viewer, &label, &day.key) else {
        return (
            StatusCode::TOO_MANY_REQUESTS,
            Html(page(DAILY_LIMIT_TITLE, daily_limit_body())),
        )
            .into_response();
    };
    let mut response = (
        StatusCode::SEE_OTHER,
        Html(page(OPENING_TITLE, opening_body(&id))),
    )
        .into_response();
    let response_headers = response.headers_mut();
    response_headers.insert(
        header::LOCATION,
        run_link(&id)
            .parse()
            .expect("a derived run address is header-safe"),
    );
    // One browser's door answer is never another browser's: the address is derived from a cookie.
    response_headers.insert(
        header::CACHE_CONTROL,
        "private, no-store".parse().expect("static header value"),
    );
    response
}

/// **The run this browser is on today** — the first serial that is not already finished, or `None`
/// when every one of today's [`RUNS_PER_DAY`] is.
///
/// "Finished" is read from the OFFERING, never guessed: a native Descent whose `fate` has latched
/// offers no action at all (`NativeDescentOffering::actions` returns an empty vector the moment
/// `sim.fate != 0`), and while a run is playable it always offers its verbs, enabled or dimmed. So
/// an OPEN session with an empty action list is a run that has ended, and nothing else is.
///
/// A session this process has not opened is taken as available without asking further: it is either
/// untouched or evicted-and-persisted, and the ordinary session route resumes the latter on arrival.
/// A player who lands back on a finished-and-resumed run therefore reaches their next one on the
/// second press, because by then it is open and this walk can see that it is over.
fn current_run(
    state: &CatalogState,
    viewer: &DreggIdentity,
    label: &str,
    day: &str,
) -> Option<String> {
    for serial in 0..RUNS_PER_DAY {
        let id = run_id(label, day, serial);
        let sid = SessionId::new(id.clone());
        let over = state.run_offering(KEY, viewer, move |host| {
            host.is_open(KEY, &sid) && host.actions(KEY, &sid).is_some_and(|a| a.is_empty())
        });
        if !over {
            return Some(id);
        }
    }
    None
}

// ─────────────────────────────────────────────────────────────────────────────────────────
// WHAT A DESCENT SESSION PAGE SAYS ABOUT ITSELF
// ─────────────────────────────────────────────────────────────────────────────────────────

/// **The note under every hosted Descent board, naming whose run it is and where the reader's own
/// one lives.** `None` for every other offering, so no other surface gains a line.
///
/// This is the half of the repair that is not routing. Repointing the CTAs fixes the path a NEW
/// visitor walks; it does nothing for the reader who arrives from a bookmark, a shared link, or the
/// refusal itself — and that reader is exactly the one the old front door stranded, on a board of
/// dimmed controls with no control anywhere that started a run. Every hosted Descent page now
/// carries the way out, whether the run is theirs, somebody else's, or the named demo.
///
/// It sits OUTSIDE `#live-surface` (beside [`crate::table_door::spectator_invite`], for the same
/// reason): the enhancement script replaces that region's whole subtree on every turn, and an escape
/// hatch must not be a thing a move can delete.
pub fn run_note(key: &str, id: &str) -> Option<String> {
    if key != KEY {
        return None;
    }
    let body = if is_own_run(id) {
        // ⚑ **WORDED FOR BOTH READERS, BECAUSE THE PREFIX DOES NOT KNOW WHO IS LOOKING.** This
        // branch fires on the ID, and a `dr1-` link can be pasted to anybody: the surface discloses
        // a hosted run to whoever holds its address and says so. An earlier draft opened "This run
        // is yours", which is a sentence that would have been FALSE for exactly the reader who most
        // needs the door. Knowing better would mean threading the viewer's LABEL through
        // `offering_page` and three transports, to buy a possessive pronoun; instead the copy states
        // the property that holds either way, and hands both readers the same working control.
        format!(
            "<h2>Your own run</h2>\
             <p class=\"prose\">This board was opened from the Descent's door, so it belongs to the \
             browser that opened it and only that browser can move in it. Anybody holding the link \
             can read it.</p>\
             <p class=\"prose\">The door brings that browser back here while the run is going, and \
             opens a fresh run once it has ended.</p>{go}",
            go = go_link(),
        )
    } else if id == DEMO_RUN {
        format!(
            "<h2>This is the demo run, not yours</h2>\
             <p class=\"prose\">One run at a fixed address, shared by everyone who opens this link. \
             A Descent belongs to one player, so this one belongs to whoever moved in it first: \
             anybody else can read it and nobody else can play it. It is kept as something to look \
             at, and nothing on this surface sends a player here to play.</p>\
             <p class=\"prose\"><strong>Your own run is one press away.</strong> It opens on \
             today's dungeon, it is yours to move in, and it is a different board from this \
             one.</p>{go}",
            go = go_link(),
        )
    } else {
        format!(
            "<h2>Whose run is this?</h2>\
             <p class=\"prose\">This is a Descent at an address somebody typed or shared rather \
             than one this game opened. It belongs to whoever made the first move in it, and \
             anybody holding the link can read it.</p>{go}",
            go = go_link(),
        )
    };
    Some(format!(
        "<section class=\"panel descent-run-note\">{body}</section>"
    ))
}

/// The door link, in the one shape every page that offers it uses. Phrased so it is the right
/// offer to a reader on their own board (it brings them back, or opens their next one) and to a
/// reader on somebody else's (it opens theirs).
fn go_link() -> String {
    format!(
        "<p><a class=\"seat-link\" href=\"{DESCENT_RUN_PATH}\">Open my run \
         <span aria-hidden=\"true\">→</span></a></p>"
    )
}

// ─────────────────────────────────────────────────────────────────────────────────────────
// THE PAGES — bodies separately, so the copy gates read the WORDS and not the stylesheet
// ─────────────────────────────────────────────────────────────────────────────────────────

const OPENING_TITLE: &str = "opening your run";
const NO_IDENTITY_TITLE: &str = "no run was opened";
const DAILY_LIMIT_TITLE: &str = "today's runs are played";

fn page(title: &str, body: String) -> String {
    document(
        &format!("{} · {title}", crate::PRODUCT_NAME),
        "descent",
        &body,
    )
}

/// The 303 body. A browser follows the `Location`; this is what a client that does not reads.
fn opening_body(id: &str) -> String {
    format!(
        "<main class=\"session af-table\">\
         <div class=\"notice ok\" role=\"status\">Opening your run.</div>\
         <p class=\"prose\"><a class=\"backlink\" href=\"{run}\">Go to the board \
         <span aria-hidden=\"true\">→</span></a></p></main>",
        run = esc(&run_link(id)),
    )
}

/// The page a caller with no durable browser name gets. It is not a scolding and not a login wall:
/// the ordinary browser that arrives here has a name minted for it on this very request, so the only
/// readers who reach it are a client that drops cookies and a caller who hand-asserted a name this
/// server never issued.
fn no_identity_body() -> String {
    format!(
        "<main class=\"session af-table\">\
         <div class=\"page-head\" style=\"padding-top:var(--s4)\"><h1>No run was opened</h1></div>\
         <div class=\"notice refused\" role=\"status\">A run has to be filed under a name this \
         browser keeps, so that it is still yours when you come back. This browser is not keeping \
         one, so nothing was opened and nothing was lost.</div>\
         <p class=\"prose\">If you turned cookies off for this site, turn them back on and press \
         the button again. If you reached this page with a name in the address bar, drop it: the \
         name this browser already holds is the one your run goes under.</p>\
         <p class=\"prose\">The other way in keeps nothing here at all. \
         <a href=\"{play}?engine=browser\">Run the whole game inside your own tab</a>, where the \
         run lives in your browser instead of on this server.</p>\
         <p class=\"prose\"><a class=\"backlink\" href=\"{play}\">← The Descent</a></p>\
         </main>",
        play = crate::DESCENT_PLAY_PATH,
    )
}

/// The page a browser that has played out all of today's hosted runs gets. It states the ceiling as
/// a number, says the runs already played are all still readable, and names the engine that has no
/// ceiling, rather than redirecting into a finished board and calling that a start.
fn daily_limit_body() -> String {
    format!(
        "<main class=\"session af-table\">\
         <div class=\"page-head\" style=\"padding-top:var(--s4)\"><h1>That was today's last run</h1>\
         </div>\
         <div class=\"notice refused\" role=\"status\">This browser has played {runs} Descents \
         today, which is all this server holds open for one browser in a day. Nothing was lost: \
         every one of those runs is still where you left it.</div>\
         <p class=\"prose\">A new dungeon is drawn every day, and tomorrow's is yours from the same \
         button.</p>\
         <p class=\"prose\"><strong>If you want another one today</strong>, \
         <a href=\"{play}?engine=browser\">run the whole game inside your own tab</a>. It is the \
         same dungeon under the same rules, this server does not hold it open, and it is not \
         counted here.</p>\
         <p class=\"prose\"><a class=\"backlink\" href=\"/you\">Open your games and runs \
         <span aria-hidden=\"true\">→</span></a></p>\
         </main>",
        runs = RUNS_PER_DAY,
        play = crate::DESCENT_PLAY_PATH,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_offerings::refusal::audit_player_text;

    /// The words a reader actually sees: tag spans removed, entities folded back. Deliberately
    /// applied to the BODY builders rather than to [`page`] output, because a whole document
    /// carries the site stylesheet and `::before` would trip the copy gate's Rust-path rule on CSS.
    fn visible_text(html: &str) -> String {
        let mut out = String::with_capacity(html.len());
        let mut depth = 0usize;
        for ch in html.chars() {
            match ch {
                '<' => depth += 1,
                '>' => depth = depth.saturating_sub(1),
                _ if depth == 0 => out.push(ch),
                _ => {}
            }
        }
        out.replace("&amp;", "&")
            .replace("&quot;", "\"")
            .replace("&lt;", "<")
            .replace("&gt;", ">")
    }

    #[test]
    fn a_run_address_is_per_browser_per_day_per_serial_and_stable() {
        let a = run_id("visitor-aaaa", "2026-07-26", 0);
        let b = run_id("visitor-bbbb", "2026-07-26", 0);
        let tomorrow = run_id("visitor-aaaa", "2026-07-27", 0);
        let second = run_id("visitor-aaaa", "2026-07-26", 1);
        assert_eq!(
            a,
            run_id("visitor-aaaa", "2026-07-26", 0),
            "the door is a navigation, not a mint: the same browser is sent to the same run"
        );
        for other in [&b, &tomorrow, &second] {
            assert_ne!(
                &a, other,
                "a different browser/day/serial is a different run"
            );
        }
        assert!(is_own_run(&a) && a.starts_with("dr1-0-"));
        assert!(second.starts_with("dr1-1-"));
        // ⚑ The label must not be recoverable from the address, and a separator-free concatenation
        // would put two different browsers on one run.
        assert!(!a.contains("visitor"));
        assert_ne!(
            run_id("ab", "cd", 0),
            run_id("a", "bcd", 0),
            "the separators are what keep two labels off one run"
        );
    }

    #[test]
    fn the_demo_run_and_an_ad_hoc_id_are_not_doors() {
        assert!(!is_own_run(DEMO_RUN));
        assert!(!is_own_run("mine"));
        assert!(!is_own_run("descent-web-2"));
    }

    /// ⚑ **EVERY HOSTED DESCENT PAGE CARRIES THE WAY OUT, AND NO OTHER OFFERING GAINS A LINE.**
    /// The state this repair exists for is a reader on a board that is not theirs: the note must
    /// name that, and it must hand them the door.
    #[test]
    fn the_note_names_the_session_and_offers_the_door() {
        let demo = run_note(KEY, DEMO_RUN).expect("the demo run says what it is");
        assert!(demo.contains("not yours"), "{demo}");
        assert!(
            demo.contains(&format!("href=\"{DESCENT_RUN_PATH}\"")),
            "the stranded reader is handed the door: {demo}"
        );
        let adhoc = run_note(KEY, "somebody-elses-link").expect("an ad-hoc id says what it is");
        assert!(
            adhoc.contains(&format!("href=\"{DESCENT_RUN_PATH}\"")),
            "{adhoc}"
        );

        // ⚑ **THE NOTE ON A DOOR-OPENED RUN MUST BE TRUE TO A READER WHO IS NOT ITS OWNER**, since
        // the branch keys on the id and a `dr1-` link can be pasted to anybody. No possessive
        // claim about the reader, and the same working control either way.
        let mine = run_note(KEY, &run_id("visitor-aaaa", "2026-07-26", 0)).expect("own run");
        assert!(mine.contains("Your own run"), "{mine}");
        assert!(
            mine.contains("belongs to the browser that opened it"),
            "the note states a property of the BOARD, never of the reader: {mine}"
        );
        for pronoun_claim in ["This run is yours", "you opened", "your browser opened"] {
            assert!(
                !mine.contains(pronoun_claim),
                "a shared link would make `{pronoun_claim}` a lie to the reader who most needs the \
                 door: {mine}"
            );
        }
        assert!(
            mine.contains(&format!("href=\"{DESCENT_RUN_PATH}\"")),
            "…and both readers get the control: it resumes an owner and opens a stranger's own \
             run: {mine}"
        );

        for other in ["automatafl", "tug", "council", "market", "dungeon"] {
            assert!(
                run_note(other, "anything").is_none(),
                "{other} must not grow a Descent line"
            );
        }
    }

    /// ⚑ The two refusals this door can serve are refusals a PLAYER can act on — driven through
    /// the shared gate (`dreggnet_offerings::refusal::audit_player_text`) rather than eyeballed.
    #[test]
    fn the_door_refusals_pass_the_refusal_copy_gate() {
        for body in [no_identity_body(), daily_limit_body()] {
            let text = visible_text(&body);
            assert_eq!(
                audit_player_text(&text, true, true),
                Vec::new(),
                "the door's refusal copy must pass the house gate: {text}"
            );
        }
    }

    /// ⚑ **NO EM-DASH IN PLAYER COPY** (`scripts/check-player-copy-punctuation.py` fails the build
    /// on one). Pinned here as well as in the script so the gate bites in the crate that owns the
    /// words.
    #[test]
    fn the_door_copy_carries_no_em_dash() {
        let mut copy = vec![
            no_identity_body(),
            daily_limit_body(),
            opening_body("dr1-0-abc"),
        ];
        for id in [DEMO_RUN, "ad-hoc", "dr1-0-abc"] {
            copy.push(run_note(KEY, id).expect("a descent note"));
        }
        for text in copy {
            let text = visible_text(&text);
            assert!(!text.contains('\u{2014}'), "em-dash in player copy: {text}");
        }
    }
}
