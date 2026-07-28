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
//! * `GET  /tug`                  — the "open a table" CTA, then the rules (that order, deliberately;
//!   see [`rules_html`]);
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
//! ## What a tug player decides — READ THIS BEFORE WRITING ANY COPY
//!
//! ⚑ THIS SECTION USED TO DESCRIBE AN ENGINE THAT NO LONGER EXISTS, and it said so in the register
//! of a standing wound: a hardcoded `[ActionKind; 4]` order, engine-chosen cards
//! (`pick_lowest`/`pick_highest`), and a `max_by_key(INFLUENCE)` standing in for the opponent — "a
//! whole tug match is a function of the deal seed". All three are gone (see
//! `dregg-multiway-tug/src/reference.rs`'s own header): the seat chooses WHICH action, THE CUT it
//! presents, and — answering — WHICH SIDE it takes, each licensed by a theorem in
//! `metatheory/Dregg2/Games/MultiwayTug.lean`. `tug_web`'s own
//! `the_rules_describe_the_decisions_the_engine_actually_offers` already checks the copy against the
//! live decision space rather than against these sentences, which is why the lie survived here.
//!
//! What the copy below must still be honest about:
//!
//! * ⚑ **A play does not move the lanes.** Only a RESPONSE (which places an escrowed cut) and the
//!   final REVEAL & SCORE (which turns each Secret up onto its owner's side) touch a lane counter. A
//!   Secret moves nothing until scoring; a Discard's favors leave the round and score for nobody. A
//!   page that does not say this reads as broken to a first-time player, who presses a button and
//!   watches all seven rows come back identical (`docs/reference/UX-QA-SWEEP-2026-07-26.md`).
//! * a round is ONE round — no match, no alternating opener, and the seat answering the last cut has
//!   a real measured edge;
//! * the hidden hand hides by non-reveal plus a Poseidon2 commitment the executor checks membership
//!   against; the host can read both hands.

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
    // The seat/spectator prose lives on `LOCK` (`table_seats::TUG`), not here: the seated table page
    // prints the spectator sentence too, and it cannot reach a door.
    table_router(TableDoor {
        lock: LOCK,
        catalog: state,
        landing: landing_page,
    })
}

/// The rules block — **staged**, not shortened by subtraction.
///
/// ⚑ **WHAT A FIRST MOVE NEEDS IS VISIBLE; THE REST COSTS ONE CLICK AND IS STILL SERVED.** This was
/// one `<h2>The rules, in one screen</h2>` over six long `<li>`s and three paragraphs: measured, 715
/// words of prose against exactly ONE form control on the whole page, and 135 words a reader passed
/// before reaching it. "One screen" had stopped being true, and a stranger's report was the plain
/// one: an impenetrable wall of text.
///
/// Every claim that was here is still here and NOTHING was traded for brevity. What changed is
/// staging. Above the fold is the shape of one turn, as a précis: the lanes and what they pay, the
/// hand, the four actions, the cut, and the ⚑ that a move does not move the lanes. Behind a
/// `<details>` is everything a player wants only once they are playing: the conservation tooth, how
/// the fog is actually held, how the round is scored and adjudicated, what the executor re-checks,
/// and what this build is honest about not being.
///
/// ⚠ Be exact about what that cost. The précis RESTATES in shorter form what the deferred block
/// states in full, so the page's served word count went UP, 715 → 784, not down. The number that
/// moved the right way is what a reader is CONFRONTED with: 715 visible words became 410, and the
/// 135 words standing between a stranger and the first control became 48. Two bullets were tightened
/// where the précis and the full statement said the same thing twice; no claim was dropped to do it.
///
/// `<details>` is the shape used for exactly this reason elsewhere in this crate (`.receipt-gloss`,
/// `.af-moves`): it is native, it needs no script, and a collapsed one still **prints and reads
/// whole** — so the served HTML, the printed page and a screen reader's document all carry every
/// sentence a reader could have found before. A claim behind a summary is deferred, not deleted.
/// ⚠ The `⚑` bullet stays OPEN on purpose: this module's own header records that a page which does
/// not say it "reads as broken to a first-time player, who presses a button and watches all seven
/// rows come back identical". That is the one rule whose absence looks like a bug, so it cannot be
/// the one rule behind a click.
fn rules_html() -> String {
    let guilds = dregg_multiway_tug::reference::N_GUILDS;
    let deck = dregg_multiway_tug::reference::DECK_SIZE;
    format!(
        "<section class=\"panel\"><h2>How one turn goes</h2>\
         <ul class=\"rules\">\
         <li><strong>{guilds} lanes, weighted <code>2 2 2 3 3 4 5</code>.</strong> Lead a lane when \
         the round ends and you take its whole weight.</li>\
         <li><strong>You hold six favor cards, hidden.</strong> Every favor belongs to one lane: \
         that is the lane it pulls. Your opponent sees how many you hold, never which.</li>\
         <li><strong>On your turn, spend ONE of four actions</strong> · Secret (1 card), Discard \
         (2), Gift (3), Competition (4). Each is once per round, so the order is yours to \
         choose.</li>\
         <li><strong>A Gift or a Competition only PRESENTS favors.</strong> You cut; your opponent \
         chooses which side they take, and you cannot answer your own cut. That is the whole \
         game.</li>\
         <li>⚑ <strong>Spending an action does not move the lanes.</strong> This is the part that \
         looks broken and is not. A <strong>Secret</strong> goes face down and reaches no lane \
         until the reveal. A <strong>Discard</strong> burns two favors out of the round and they \
         reach no lane ever. A <strong>Gift</strong> or <strong>Competition</strong> puts its \
         favors in escrow, and they land on the two sides only when your opponent ANSWERS. So the \
         seven lane rows will often sit perfectly still right after your own move: that is the \
         rules working. The running account of where all {deck} favors are (held, face down, \
         burnt, placed) is what moves, and the table prints it.</li>\
         </ul>\
         <details class=\"rules-more\"><summary>All of it: the deck, the hidden hand, scoring, and \
         what this build does not do</summary>\
         <ul class=\"rules\">\
         <li><strong>{guilds} guilds are the {guilds} lanes</strong> · one thing, two names, and \
         this page uses both: guild 3 <em>is</em> lane 3. There are {deck} <strong>favor \
         cards</strong> in all: a favor <em>is</em> a card. That {deck} is fixed for the whole \
         round: no favor is conjured or destroyed, and a move that would do either is refused.</li>\
         <li><strong>How the hand is hidden.</strong> Beside the count, your opponent sees the \
         committed root of your hand; the cards themselves are rendered to you and to nobody else. \
         What a lane pays is what it pays whoever ends up leading it.</li>\
         <li><strong>Nothing ends the round early.</strong> All twelve committed turns are always \
         played, and the winner is named once, at the reveal. The bars pick <em>which rule</em> \
         names them: 11 influence takes it outright, else leading 4 lanes. Short of either bar the \
         round is still decided, on the higher total influence, else the more lanes held; and only \
         an exact dead heat on both is a draw. Every one of those clauses is enforced: a claimed \
         win the rules do not make is refused.</li>\
         <li><strong>Then reveal and score.</strong> Each seat's Secret is turned face up onto its \
         owner's side of its lane, and only then is control counted.</li>\
         <li><strong>The shape of the round is yours.</strong> Which of your four actions to spend, \
         in which order, and which cards to put in the cut, are all yours.</li>\
         </ul>\
         <p class=\"prose\">Every play is checked against the rules and against your own dealt \
         hand, so a hidden hand is still not a hand you can invent cards from. Every press is \
         re-run against the rules before anything is written down. The move and the proof that the \
         card came from your own dealt hand land together or not at all, a press out of turn is \
         refused with nothing recorded, and the whole round can be replayed afterwards from its \
         accepted moves and come out the same way.</p>\
         <p class=\"prose\"><strong>Honest about the play:</strong> a round is one round. There \
         is no match, no alternating opener, and the seat that answers the last cut has a real \
         measured edge. And the winner is not this page's opinion: the rules decide it, and if \
         they cannot, the round refuses to end rather than name somebody.</p>\
         </details>\
         <p class=\"prose credit-line\">Mechanics derived from Hanamikoji (Kota Nakayama); this is \
         an original re-theming.</p>\
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
         <p class=\"deck\">Two hidden hands of cards pulling at seven contested lanes. You cut the \
         offer; your opponent chooses which side they take.</p>\
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
    document(
        &format!("{} · Multiway-Tug", crate::PRODUCT_NAME),
        "offerings",
        &body,
    )
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
