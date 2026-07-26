//! # The **multiway-tug table** — the front door the tug never had.
//!
//! Before this module, two people could not reliably start a game of multiway-tug. There was no
//! minting route, no seat lock, no invite and no spectator view; the catalog page pointed every
//! visitor at ONE publicly-guessable table (`/offerings/tug/session/tug-web`) where the first two
//! identities to press a button took the seats and everybody after them was told they were a
//! spectator. On Discord that shape works because the channel *is* the room. On the open web it is
//! a race condition wearing a lobby's clothes — and worse for a hidden-hand game, because the
//! catalog's identity is an ASSERTED label, so asserting the opponent's label rendered the
//! opponent's hand.
//!
//! The door itself lives in [`crate::table_door`] and the seat derivation in
//! [`crate::table_seats`] — the SAME code automatafl's door runs, not a copy of it. This module is
//! the tug-specific half: the rules copy and the landing page.
//!
//! * `GET  /tug`                  — the rules + the "open a table" CTA;
//! * `POST /tug/table`            — MINT `tug1-<96 random bits>` plus two secret seat links;
//! * `GET  /tug/table/{id}`       — a seat link (`?seat=&key=`, checked, then the label becomes an
//!   `HttpOnly` cookie and the secret leaves the URL bar);
//! * `POST /tug/table/{id}/resign`— end your own table;
//! * `GET  /tug/watch/{id}`       — SPECTATE with BOTH hands fogged;
//! * `GET  /tug/watch/{id}/events`— the spectator's realtime stream.
//!
//! ## What the fog is here
//!
//! [`dregg_multiway_tug::surface::TugSession::surface_for`] paints a viewer's own hand as exact
//! card ids and every other hand as `count + committed root` (a Poseidon2 [`HandTree`] root). The
//! spectator route renders as an identity holding no seat, so it takes the `None` branch and BOTH
//! hands are the fog form. That much is a real per-viewer projection over a real commitment.
//!
//! ## What a tug player currently decides — READ THIS BEFORE WRITING ANY COPY
//!
//! Almost nothing, and the pages here must not pretend otherwise. Verified at the definitions in
//! `dregg-multiway-tug/src/reference.rs`:
//!
//! * the four actions are played in a FIXED schedule (`Engine::order` is a hardcoded
//!   `[ActionKind; 4]`, identical for both seats; `play_next` reads `order[order_pos[p]]`), and
//!   `TugOffering::advance` refuses anything that is not `peek_next_action()` — so the player does
//!   not choose which action to play, only when to press it;
//! * which CARDS an action spends is chosen by the engine (`pick_lowest` / `pick_highest`), not by
//!   the player — `advance` takes no card argument at all;
//! * the "opponent's blind pick" that `lib.rs` and `reference.rs` describe as *"a real choice"* /
//!   *"an adversarial decision made by the other agent"* is [`dregg_multiway_tug::reference`]'s
//!   `opponent_gift_pick` / `opponent_comp_pick`: `max_by_key(INFLUENCE)` and a two-way weight
//!   comparison. Deterministic functions of the presented cards. Nobody decides anything.
//!
//! A whole tug match is therefore a function of the deal seed, and the eight presses are the two
//! players taking turns advancing a movie. That is a REAL wound in the game and it is not this
//! module's to fix — but a front door that advertised "outplay your opponent" would be a lie, so
//! the rules copy below says what the game currently is.

use std::sync::Arc;

use axum::Router;
use axum::http::header;
use axum::response::{IntoResponse, Response};
use axum::routing::get;

use crate::table_door::{TableDoor, open_a_table_section, table_router};
use crate::table_seats::{self, TableLock};
use crate::{CatalogState, document, esc};

/// The catalog key this surface plays.
pub const KEY: &str = table_seats::TUG.key;

/// The prefix a SEAT-LOCKED (lobby-minted) tug table id wears.
pub const TABLE_PREFIX: &str = table_seats::TUG.table_prefix;

/// The tug seat lock — the id/label derivation and the act-path gate.
pub const LOCK: TableLock = table_seats::TUG;

/// **Assemble the multiway-tug front door.** Merged into the demo app by `make_app`; additive — it
/// adds no route that overlaps the catalog's `/offerings/**` surface.
pub fn tug_router(state: Arc<CatalogState>) -> Router {
    Router::new()
        .route("/tug/art/exchange.jpg", get(get_exchange_art))
        .merge(tug_door(state))
}

/// **The tug's hero painting** — spwashi's `exchange`: two pairs of hands on a strung brass
/// balance, a violet knot pulled taut in the middle. The game is two houses pulling at shared
/// lanes, so it is the painting rather than a decoration. Compiled INTO the binary
/// (`include_bytes!`, the same way `/automatafl/art/gametable.jpg` is served), so the landing has no
/// external asset, no `ServeDir`, no file-system read at request time and a trivial CSP story.
const EXCHANGE_JPEG: &[u8] = include_bytes!("../../assets/games/multiway-tug/hero/exchange.jpg");

/// `GET /tug/art/exchange.jpg` — the landing hero's backdrop.
async fn get_exchange_art() -> Response {
    (
        [
            (header::CONTENT_TYPE, "image/jpeg"),
            (header::CACHE_CONTROL, "public, max-age=604800, immutable"),
        ],
        EXCHANGE_JPEG,
    )
        .into_response()
}

fn tug_door(state: Arc<CatalogState>) -> Router {
    table_router(TableDoor {
        lock: LOCK,
        catalog: state,
        landing: landing_page,
        seat_note: "(Which side you get — seat A or seat B — is settled by the game when you make \
                    your first move; the link decides only that the table is <em>yours</em>.)",
        spectator_note: "Spectators see the guild lanes and the score with BOTH hands fogged — a \
                         card count and each hand's committed root, never a card — and every \
                         control inert.",
    })
}

/// The rules block — what a stranger needs to know before their first click, and no more.
fn rules_html() -> String {
    let guilds = dregg_multiway_tug::reference::N_GUILDS;
    let deck = dregg_multiway_tug::reference::DECK_SIZE;
    format!(
        "<section class=\"panel\"><h2>The rules, in one screen</h2>\
         <ul class=\"rules\">\
         <li><strong>{guilds} guilds</strong> are contested, weighted <code>2 2 2 3 3 4 5</code> — \
         {deck} favor cards in all, and that {deck} is a conservation tooth the executor enforces: \
         no favor is conjured or destroyed for the length of a round.</li>\
         <li><strong>Each seat holds six favors</strong>, hidden. Your opponent sees only how many \
         cards you hold and the committed root of your hand; the cards themselves are rendered to \
         you and to nobody else.</li>\
         <li><strong>Four actions, once each per round</strong> — Secret, Discard, Gift, \
         Competition — spending 1, 2, 3 and 4 cards. Whoever leads a guild lane takes its weight. \
         <strong>Win at 11 influence or 4 guilds</strong>; short of that the round is still \
         decided — on total influence, then on lanes held — and only an exact dead heat on both \
         is a draw. Every one of those clauses is a tooth: the executor refuses a claimed win the \
         rules do not make.</li>\
         <li><strong>A Gift or a Competition only PRESENTS favors.</strong> You cut; your opponent \
         chooses which side they take, and you cannot answer your own cut. Which of your four \
         actions to spend, in which order, and which cards to put in the cut, are all yours.</li>\
         <li><strong>Then reveal and score.</strong> The Secret is turned face up onto its owner's \
         side before control is counted.</li>\
         </ul>\
         <p class=\"prose\">Every press is one real executor turn: the rules action and the \
         hidden-hand membership witness land together or not at all, an out-of-order press is \
         REFUSED with nothing committed, and the whole round re-verifies by replaying every \
         accepted input through a fresh executor.</p>\
         <p class=\"prose\"><strong>Honest about the play:</strong> a round is one round — there \
         is no match, no alternating opener, and the seat that answers the last cut has a real \
         measured edge. The rules themselves are authored in Lean and the winner is decided by \
         that proof, not by this page.</p>\
         <p class=\"prose\">Mechanics derived from Hanamikoji (Kota Nakayama); this is an original \
         re-theming.</p>\
         </section>"
    )
}

/// `GET /tug` — the landing page.
fn landing_page(notice: Option<&str>) -> String {
    let body = format!(
        "<main class=\"session af-table\">\
         <section class=\"af-hero hero-tug\">\
         <p class=\"eyebrow\">Hidden hands · seven guilds · one round</p>\
         <h1>Multiway-Tug</h1>\
         <p class=\"deck\">Two houses pull at seven guilds with favors neither can see the other \
         holding. Every play is a real executor turn carrying its own membership witness — the \
         hand stays hidden and the round still proves.</p>\
         <p class=\"credit\">Art · spwashi, <em>exchange</em></p>\
         </section>\
         {notice}\
         {open}\
         {rules}\
         <p class=\"prose\"><a class=\"backlink\" href=\"/offerings\">← All games</a></p>\
         </main>",
        notice = notice
            .map(|n| format!(
                "<div class=\"notice refused\" role=\"status\">{}</div>",
                esc(n)
            ))
            .unwrap_or_default(),
        open = open_a_table_section(&LOCK),
        rules = rules_html(),
    );
    document("dregg — Multiway-Tug", "offerings", &body)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::table_seats::SeatSlot;

    #[test]
    fn the_landing_mints_a_table_and_never_advertises_the_old_shared_one() {
        let page = landing_page(None);
        assert!(page.contains("action=\"/tug/table\""));
        assert!(
            !page.contains("/offerings/tug/session/tug-web"),
            "the global tug table is gone; nothing may point at it"
        );
    }

    /// ⚑ This test used to PIN THE MARKETING COPY: it asserted the page still contained the
    /// strings "does not yet choose" and "the engine picks the cards". Those sentences described
    /// an engine that had already been replaced — a hardcoded action order and a `max_by_key`
    /// standing in for the opponent — so the test stayed green while the page UNDERSTATED the
    /// game, and it would have gone red if anyone corrected the page. A test that pins prose
    /// rather than behaviour is a lock on the documentation, not a check of it.
    ///
    /// What it checks now is the property the old test was reaching for — that the copy does not
    /// promise more than the build has — stated against the CODE rather than against a sentence:
    /// the seat really does choose (the decision space is bigger than one), and the rules block
    /// says so.
    #[test]
    fn the_rules_describe_the_decisions_the_engine_actually_offers() {
        let rules = rules_html();
        // The seat genuinely chooses: a fresh round offers a real decision space, not a schedule.
        let engine = dregg_multiway_tug::reference::Engine::new(1);
        let options = engine.legal_decisions();
        assert!(
            options.len() > 1,
            "the engine offers {} decisions — if it is back to a schedule the copy below is a lie",
            options.len()
        );
        assert!(
            rules.contains(
                "your opponent \
         chooses which side they take"
            ),
            "the cut/choose step must be disclosed: {rules}"
        );
        // The round is DECIDED short of a threshold, and the page must not still claim otherwise.
        assert!(
            rules.contains(
                "the round is still \
         decided"
            ),
            "the adjudication must be disclosed: {rules}"
        );
        assert!(
            !rules.contains("does not yet choose") && !rules.contains("engine picks the cards"),
            "the page still carries the retired no-decisions disclosure: {rules}"
        );
        for lie in ["outplay your opponent", "bluff", "read your opponent"] {
            assert!(!rules.contains(lie), "the rules copy promises `{lie}`");
        }
    }

    #[test]
    fn the_key_and_prefix_are_the_lock_s_and_do_not_collide_with_automatafl() {
        assert_eq!(KEY, "tug");
        assert_eq!(TABLE_PREFIX, "tug1-");
        let id = LOCK.mint_table_id();
        assert!(id.starts_with(TABLE_PREFIX));
        assert_eq!(
            LOCK.seat_of_label(&id, &LOCK.seat_label(&id, SeatSlot::B)),
            Some(SeatSlot::B)
        );
        assert_eq!(
            crate::automatafl_web::LOCK.seat_of_label(&id, &LOCK.seat_label(&id, SeatSlot::B)),
            None,
            "an automatafl lock must not open a tug seat"
        );
    }
}
