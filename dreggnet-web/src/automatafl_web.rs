//! # The **automatafl table** — the bespoke web surface over the generic offering rails.
//!
//! Automatafl was already PLAYABLE at `/offerings/automatafl/session/{id}` (real commit/reveal,
//! per-viewer sealed-move fog, executor-refused illegal moves, a `TurnReceipt` per advance), but it
//! ran on the generic catalog rails with no front door: no rules page, no way to mint a table and
//! hand someone a link, no spectator view, and — the defect that actually broke the game — no
//! realtime, so in a SIMULTANEOUS-MOVE game the waiting seat had to hammer reload to learn that the
//! opponent had sealed, opened, or resolved.
//!
//! This module is now only the automatafl-SPECIFIC half of that front door — the rules copy, the
//! board still, the hero art. The door itself (mint / seat link / resign / spectate / stream) is
//! [`crate::table_door`], driven by the [`crate::table_seats::AUTOMATAFL`] lock, because the tug
//! needed exactly the same door and a second implementation of seat authorisation is worse than
//! none.
//!
//! * `GET  /automatafl`                  — the rules + the "open a table" CTA;
//! * `POST /automatafl/table`            — MINT a table: an unguessable session id plus two
//!   unguessable per-seat links (yours + the one you send your opponent);
//! * `GET  /automatafl/table/{id}`       — a seat link;
//! * `POST /automatafl/table/{id}/resign`— end your own table;
//! * `GET  /automatafl/watch/{id}`       — SPECTATE (both sealed moves are fog, controls inert);
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
//! `render_for` discloses to whoever claims to be them. A table MINTED HERE closes that
//! structurally; the mechanism and its exact residue are documented on [`crate::table_seats`].
//!
//! ## What the seal is, and what it is not
//!
//! The sealed move HIDES BY NON-REVEAL ON A TRUSTED HOST. [`dregg_automatafl::surface`] stores the
//! move's plaintext server-side at commit time and simply declines to render it to the opponent
//! until the reveal; the executor holds a commitment, but the two clients share no cryptographic
//! commitment and the host can read both moves. The crate says so in its own header. Nothing on
//! these pages may imply otherwise.

use std::sync::Arc;

use axum::Router;
use axum::http::header;
use axum::response::{IntoResponse, Response};
use axum::routing::get;

use crate::table_door::{TableDoor, open_a_table_section, table_router};
use crate::table_seats::{self, TableLock};
use crate::{CatalogState, document, esc};

/// The catalog key the bespoke surface plays.
pub const KEY: &str = table_seats::AUTOMATAFL.key;

/// The prefix a SEAT-LOCKED (lobby-minted) table id wears.
pub const TABLE_PREFIX: &str = table_seats::AUTOMATAFL.table_prefix;

/// The automatafl seat lock — the id/label derivation and the act-path gate.
pub const LOCK: TableLock = table_seats::AUTOMATAFL;

pub use crate::table_seats::SeatSlot;

/// Mint a seat-locked automatafl table id (`af1-` + 96 random bits) — [`LOCK`]'s minter, kept as a
/// free function because that is how the table test and every existing caller reach it.
pub fn mint_table_id() -> String {
    LOCK.mint_table_id()
}

/// The secret label for `seat` at automatafl table `id` — see [`crate::table_seats::TableLock`].
pub fn seat_label(id: &str, seat: SeatSlot) -> String {
    LOCK.seat_label(id, seat)
}

/// The seat `label` holds at automatafl table `id`, if any.
pub fn seat_of_label(id: &str, label: &str) -> Option<SeatSlot> {
    LOCK.seat_of_label(id, label)
}

/// The seat link for `seat` at automatafl table `id`.
pub fn seat_link(id: &str, seat: SeatSlot) -> String {
    LOCK.seat_link(id, seat)
}

/// Whether `id` names a seat-locked automatafl table.
pub fn is_locked_table(id: &str) -> bool {
    LOCK.is_locked_table(id)
}

/// **Assemble the automatafl front door.** Merged into the demo app by `make_app`; additive — it
/// adds no route that overlaps the catalog's `/offerings/**` surface.
pub fn automatafl_router(state: Arc<CatalogState>) -> Router {
    Router::new()
        .route("/automatafl/art/gametable.jpg", get(get_gametable_art))
        // The seat/spectator prose lives on `LOCK` (`table_seats::AUTOMATAFL`), not here: the
        // seated table page prints the spectator sentence too, and it cannot reach a door.
        .merge(table_router(TableDoor {
            lock: LOCK,
            catalog: state,
            landing: landing_page,
        }))
}

/// **The games hero** — spwashi's `gametable` (an overhead table, dancers leaving traced paths),
/// the brand's own painting for exactly this page. Compiled INTO the binary (`include_bytes!`), so
/// the landing has no external asset dependency, no file-system read at request time and no
/// `ServeDir` on the deployment: the byte string is served straight out of the image. Immutable —
/// the content only changes when the binary does.
const GAMETABLE_JPEG: &[u8] = include_bytes!("../../assets/games/automatafl/board/gametable.jpg");

/// `GET /automatafl/art/gametable.jpg` — the landing hero's backdrop.
async fn get_gametable_art() -> Response {
    (
        [
            (header::CONTENT_TYPE, "image/jpeg"),
            (header::CACHE_CONTROL, "public, max-age=604800, immutable"),
        ],
        GAMETABLE_JPEG,
    )
        .into_response()
}

/// The rules block — what a stranger needs to know before their first click, and no more.
fn rules_html() -> String {
    let n = dregg_automatafl::game::N;
    format!(
        "<section class=\"panel\"><h2>The rules, in one screen</h2>\
         <ul class=\"rules\">\
         <li><strong>The board</strong> is {n}×{n}. It holds repulsors (<code>R</code> — the \
         angular pale blades, spikes pointing OUT), attractors (<code>A</code> — the round brass \
         discs, spikes pointing IN), and ONE automaton (<code>@</code> — the violet ring, the only \
         thing on the board that glows). Pieces move like a rook: any distance along a row or a \
         column, never diagonally, never onto the automaton. Either seat may push ANY piece — the \
         pieces are shared, and that is what makes the collision interesting.</li>\
         <li><strong>You do not take turns.</strong> Both seats seal a move at the same time. The \
         round runs <em>commit → reveal → resolve</em>: you seal, your opponent seals, both open, \
         then ONE turn applies both.</li>\
         <li><strong>The seal is the game.</strong> While your move is sealed your opponent is not \
         shown it — but be clear about who is doing the hiding. Your move sits on this server in \
         plain text until you open it, so what keeps it secret is this server declining to tell \
         them, not a code the two of you exchanged that nobody else can read. Trust the host or do \
         not play here.</li>\
         <li><strong>A CLASH marks the square and re-opens the round.</strong> If the two moves \
         fight over the same square, that round does not happen at all: the contested coordinate is \
         MARKED (it paints as a dead <code>×</code> square), the board FREEZES exactly as it was, \
         and the seats the clash named owe a FRESH move — which may not use a marked square at \
         either end. The turn counter does not move until a round comes back clean, and the markers \
         die when it does. Every re-entry has to burn a NEW square, so a turn cannot re-open \
         forever.</li>\
         <li><strong>The automaton then steps</strong> — once the round finally resolves — pulled \
         toward attractors and pushed from repulsors along each axis. Drive it onto one of YOUR two \
         goal corners and you win.</li>\
         </ul>\
         <p class=\"prose\">Every press is re-run against the rules before anything is written \
         down: an illegal move is refused and nothing happens. And when the match is over, anyone \
         can replay it from the first move to the last and watch it come out the same way. That \
         replay happens on this server — not on a blockchain, and no public network is \
         involved.</p>\
         </section>",
        n = n,
    )
}

/// The board itself, on the front door — the SAME painter the live table uses, on a real opening
/// position with one piece picked up. A stranger sees the game before deciding to open a table,
/// and the board's own key names every shape.
fn board_preview() -> String {
    format!(
        "<section class=\"panel\"><h2>The board</h2>\
         <p class=\"prose\">A real opening position, mid-turn: one attractor has been picked up, \
         and every square it can legally move to is lit. This is the board you get.</p>\
         {still}</section>",
        still = crate::automatafl_still(""),
    )
}

/// `GET /automatafl` — the landing page.
fn landing_page(notice: Option<&str>) -> String {
    let body = format!(
        "<main class=\"session af-table\">\
         <section class=\"af-hero\">\
         <p class=\"eyebrow\">Simultaneous moves · sealed until you both open</p>\
         <h1>Automatafl</h1>\
         <p class=\"deck\">A board game where the piece that decides it is the one neither player \
         controls. You both move at once, in the dark, and the automaton answers whatever you \
         leave standing around it.</p>\
         <p class=\"credit\">Art · spwashi, <em>gametable</em></p>\
         </section>\
         {notice}\
         {open}\
         {board}\
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
        board = board_preview(),
        rules = rules_html(),
    );
    document(
        &format!("{} — Automatafl", crate::PRODUCT_NAME),
        "offerings",
        &body,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::table_seats::SeatSlot;

    #[test]
    fn the_landing_mints_through_the_shared_door_and_never_advertises_a_shared_table() {
        let page = landing_page(None);
        assert!(page.contains("action=\"/automatafl/table\""));
        assert!(
            !page.contains("/offerings/automatafl/session/automatafl-web"),
            "the front door must not point at the old publicly-guessable shared table"
        );
    }

    /// ⚑ **A LONE VISITOR IS TOLD WHAT THIS COSTS AND WHAT ELSE THEY CAN DO — BEFORE THE BUTTON.**
    /// There is no matchmaking, no queue and no bot anywhere on this product: a table mints two seat
    /// links and you send one yourself. That was disclosed as the third sentence of a paragraph, so
    /// the predicted (and observed) path was: click a two-player game, read "send this link to your
    /// opponent", have nobody, close the tab. Two things are pinned: the requirement rides a
    /// SCANNABLE chip, and the page names an exit rather than leaving the reader at a dead end.
    #[test]
    fn the_landing_states_the_two_player_requirement_and_offers_a_way_out_of_it() {
        let page = landing_page(None);
        assert!(
            page.contains("<p class=\"needs\">Two players"),
            "the player-count requirement must be a chip a scanner reads, not buried prose: {page}"
        );
        assert!(
            page.contains("play both") && page.contains(crate::DESCENT_PLAY_PATH),
            "a visitor with nobody to invite must be handed both exits — hold both seats, or the \
             game meant for one: {page}"
        );
    }

    #[test]
    fn the_rules_do_not_claim_a_cryptographic_commitment_between_clients() {
        // `dregg-automatafl/src/surface.rs` stores the move PLAINTEXT server-side at commit time
        // (`AutomataflSession::committed: [Option<Move>; 2]`). Copy that says otherwise would be a
        // lie, so pin the honest phrasing. The wording moved out of shouted caps and into ordinary
        // words; what is pinned is the CLAIM, not the typography.
        let rules = rules_html();
        assert!(
            rules.contains("sits on this server in plain text"),
            "{rules}"
        );
        assert!(rules.contains("Trust the host"), "{rules}");
        // …and it must never upgrade itself into a claim of client-to-client cryptography.
        for lie in [
            "end-to-end",
            "encrypted",
            "the server cannot",
            "we cannot see",
        ] {
            assert!(
                !rules.contains(lie),
                "the seal copy claims `{lie}`, which the surface does not do: {rules}"
            );
        }
    }

    #[test]
    fn the_key_and_prefix_are_the_lock_s() {
        assert_eq!(KEY, "automatafl");
        assert_eq!(TABLE_PREFIX, "af1-");
        let id = LOCK.mint_table_id();
        assert!(id.starts_with(TABLE_PREFIX));
        assert_eq!(
            LOCK.seat_of_label(&id, &LOCK.seat_label(&id, SeatSlot::A)),
            Some(SeatSlot::A)
        );
    }
}
