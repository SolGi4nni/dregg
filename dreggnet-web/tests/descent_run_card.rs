//! **The shared run-card has to be worth clicking.**
//!
//! `/descent/native/run/{id}` is the link a stranger meets the game through. It used to report the
//! run as `Banked relics: 3` — a number, with no picture, no depth, no sense of what the player
//! walked past or was still carrying. This suite pins the card that replaced it, through the REAL
//! HTTP surface (submit a real record, GET the real share path), against the REAL replayed state:
//!
//! * the shaft is painted, with the play surface's own board (rows floors 1–4 then `@` then `$`,
//!   one column per relic, the same glyph alphabet);
//! * **banked and unbanked do not look the same** — a relic a proved exit made theirs paints
//!   `banked`, a relic still riding in an unfinished run's pack paints `at-risk`, and the words say
//!   which is which;
//! * the run's SHAPE is on the card — light spent of the game's own `BREATH`, depth of `FLOORS`;
//! * the link unfurls: OpenGraph / Twitter tags carry the run's one-line story, because a page
//!   whose job is to be posted is judged by what the preview says;
//! * the copyable text form is the SAME board (`deos_view::coordgrid_text`) every chat channel
//!   already paints.
//!
//! ## The glyph weld
//!
//! `native_descent`'s glyph table is private to `dreggnet-offerings`, so the card mirrors it. A
//! mirror nobody checks is a bug with a delay fuse, and here it would be a nasty one: the card and
//! the live game drawing two different alphabets for the same dungeon. Until that table is
//! exported, [`the_card_and_the_live_surface_speak_one_alphabet`] is the weld — it reads the SERVED
//! play controller's own `const GLYPH_* = "…"` declarations and requires the card's legend to carry
//! every one of them.

use std::sync::Arc;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_offerings::native_descent::{
    NativeDescentOffering, NativeDescentRecord, NativeDescentSession,
};
use dreggnet_offerings::native_descent_wire::PortableRecord;
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};
use dreggnet_web::descent_play::descent_play_router;
use dreggnet_web::{DescentState, descent_router};
use dungeon_on_dregg::descent::{BREATH, FLOORS};
use procgen_dregg::{CommittedSeed, daily_seed};
use tower::ServiceExt;

const DAY: &str = "card-day";

async fn post(
    app: &axum::Router,
    path: &str,
    body: serde_json::Value,
) -> (StatusCode, serde_json::Value) {
    let response = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri(path)
                .header("content-type", "application/json")
                .body(Body::from(body.to_string()))
                .unwrap(),
        )
        .await
        .unwrap();
    let status = response.status();
    let bytes = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .unwrap();
    let json = serde_json::from_slice(&bytes)
        .unwrap_or_else(|_| serde_json::json!({ "body": String::from_utf8_lossy(&bytes) }));
    (status, json)
}

async fn get(app: &axum::Router, path: &str) -> (StatusCode, String) {
    let response = app
        .clone()
        .oneshot(Request::builder().uri(path).body(Body::empty()).unwrap())
        .await
        .unwrap();
    let status = response.status();
    let bytes = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .unwrap();
    (status, String::from_utf8_lossy(&bytes).to_string())
}

fn native_seed_input(seed: &CommittedSeed) -> u32 {
    let bytes = seed.as_bytes();
    u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]])
}

fn land(
    offering: &NativeDescentOffering,
    session: &mut NativeDescentSession,
    actor: &str,
    turn: &str,
    arg: i64,
) {
    match offering.advance(
        session,
        Action::new(turn, turn, arg, true),
        DreggIdentity(actor.to_string()),
    ) {
        Outcome::Landed { .. } => {}
        Outcome::Refused(reason) => panic!("card fixture move {turn}({arg}) refused: {reason}"),
    }
}

/// **Drive a real crown-seeking run, planned against the executor's OWN legality list.**
///
/// The fixture used to be a literal tape (`delve, smite, loot 1, unlock 2, …`). That was a
/// hostage to the rules: the night `harm`/`lunge` landed and re-emitted the day family, a floor
/// needed a second blow, and every assertion in this file died on `loot(1) refused: the guardian
/// still stands` — a fixture failure wearing a product failure's clothes.
///
/// So the line is PLANNED, never spelled: each step reads `Offering::actions` (the
/// executor-backed `enabled` verdict, the same list the browser's board lights up from) and takes
/// the highest-priority move that is actually legal right now. The strategy is the crown line —
/// take the prize, take the way-keys, put the guardian down, open the way, go deeper — and
/// deliberately never loots a treasure, because carrying rights attenuate with depth and a greedy
/// pack cannot reach floor 4.
///
/// It therefore survives a re-drawn map, a changed guardian vitality, and a new verb. What it
/// cannot do is manufacture an illegal run: every move goes through the real executor, and the
/// caller asserts the outcome it wanted actually happened.
fn drive_crown_line(
    offering: &NativeDescentOffering,
    session: &mut NativeDescentSession,
    actor: &str,
) {
    // The crown, then the three way-keys. Never relics 4–7: a pack of treasure cannot descend.
    let wanted: [i64; 4] = [0, 1, 2, 3];
    for _ in 0..64 {
        let actions = offering.actions(session);
        let can = |turn: &str, arg: i64| {
            actions
                .iter()
                .any(|a| a.turn == turn && a.arg == arg && a.enabled)
        };

        // 1. The prize and the keys, the moment the floor's hoard opens.
        if let Some(&relic) = wanted.iter().find(|&&relic| can("loot", relic)) {
            land(offering, session, actor, "loot", relic);
            continue;
        }
        // 2. The guardian stands between us and the hoard. `smite` only — `lunge` is the cheap
        //    blow that costs a carry slot, and this line needs all four.
        if can("smite", 0) {
            land(offering, session, actor, "smite", 0);
            continue;
        }
        // 3. Exercise a carried key, then step through.
        if let Some(way) = (2..=FLOORS as i64).find(|&way| can("unlock", way)) {
            land(offering, session, actor, "unlock", way);
            continue;
        }
        if can("delve", 0) {
            land(offering, session, actor, "delve", 0);
            continue;
        }
        // 4. ⚑ THE CLIMB HOME. `flee` is illegal below the surface, so once the bottom is
        //    cleared the line pays one light per floor to get back out.
        if can("ascend", 0) {
            land(offering, session, actor, "ascend", 0);
            continue;
        }
        break;
    }
}

/// A settled crown run: the planned line, then the proved exit that banks the pack.
fn crowned_record(seed: &CommittedSeed, actor: &str) -> NativeDescentRecord {
    let offering = NativeDescentOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(u64::from(native_seed_input(seed))))
        .expect("the native day opens");
    // `drive_crown_line` already pays the climb home — `flee` is illegal below the surface.
    drive_crown_line(&offering, &mut session, actor);
    land(&offering, &mut session, actor, "flee", 0);
    let record = session.export_record();
    assert!(
        record
            .completion
            .as_ref()
            .is_some_and(|completion| completion.crowned),
        "the planned line must actually crown, or every assertion below is about a run that did \
         not happen"
    );
    record
}

/// The SAME line, abandoned one move from the exit: the pack is full and NOTHING is banked. This
/// is the common loss — far more reachable than a dead light — and the card must not dress it as
/// a haul.
fn abandoned_record(seed: &CommittedSeed, actor: &str) -> NativeDescentRecord {
    let offering = NativeDescentOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(u64::from(native_seed_input(seed))))
        .expect("the native day opens");
    drive_crown_line(&offering, &mut session, actor);
    let record = session.export_record();
    assert!(
        record.completion.is_none(),
        "an abandoned run has not settled"
    );
    let carrying = record
        .events
        .last()
        .map(|event| event.post.pack())
        .unwrap_or(0);
    assert!(
        carrying > 0,
        "the abandoned fixture must actually be CARRYING something, or the loss it is meant to \
         show is not on the card"
    );
    record
}

/// Submit a record and return its share-card HTML.
async fn card_for(app: &axum::Router, native: &NativeDescentRecord) -> String {
    let wire = serde_json::to_value(PortableRecord::from_record(native)).expect("the wire encodes");
    let (status, accepted) = post(
        app,
        "/descent/native/submit",
        serde_json::json!({ "day": DAY, "record": wire }),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "{accepted}");
    assert_eq!(accepted["verified"], true, "{accepted}");
    let share = accepted["share"].as_str().expect("a share path");
    let (card_status, card) = get(app, share).await;
    assert_eq!(card_status, StatusCode::OK);
    card
}

fn board() -> (axum::Router, CommittedSeed) {
    let seed = daily_seed(&[91; 32]);
    let state = Arc::new(DescentState::new());
    state.open_day(DAY, seed);
    (descent_router(state), seed)
}

/// **The card paints the shaft, and a proved exit LOOKS like one.** Not `Banked relics: 4` — the
/// board, with the banked relics filled solid, the run's depth and light on it, and the prize named.
#[tokio::test]
async fn a_crowned_run_card_paints_the_shaft_and_the_haul() {
    let (app, seed) = board();
    let card = card_for(&app, &crowned_record(&seed, "web:crowned")).await;

    // The board is there, and it is the LIVE board's shape: `3 + RELICS` columns.
    assert!(
        card.contains("class=\"rc-map\""),
        "the shaft is painted: {card}"
    );
    assert!(
        card.contains("grid-template-columns:repeat(11,1fr)"),
        "marker + way + guardian then ONE COLUMN PER RELIC: {card}"
    );
    // The pack row and the vault row are both on it — they are different states and must LOOK
    // different, which is the whole point of keeping both rows on a settled card. (`>` is escaped
    // in HTML, so it is matched inside its own cell rather than against every tag on the page.)
    for glyph in ["@</span>", "$</span>", "&gt;</span>"] {
        assert!(
            card.contains(glyph),
            "the `{glyph}` row marker is a cell on the board: {card}"
        );
    }
    // BANKED reads as banked: a filled cell, plus the prize NAMED.
    assert!(
        card.contains("rc-cell tag-vault banked"),
        "the banked relics are filled solid: {card}"
    );
    assert!(
        card.contains("the Crown of the Deep"),
        "the prize is named, not indexed: {card}"
    );
    assert!(
        card.contains("CROWNED"),
        "the one-word verdict is stamped: {card}"
    );

    // THE RUN'S SHAPE — light against the game's own clock, depth against the game's own floors.
    assert!(
        card.contains(&format!("<span class=\"rc-of\">/{BREATH}</span>")),
        "the light is shown against the game's BREATH ({BREATH}): {card}"
    );
    assert!(
        card.contains(&format!("<span class=\"rc-of\">/{FLOORS}</span>")),
        "the depth is shown against the game's FLOORS ({FLOORS}): {card}"
    );
    assert!(
        card.contains("light left") && card.contains("depth reached"),
        "the stats are labelled in the player's language: {card}"
    );

    // The loss EVERY run takes: the carry cap means treasure was walked past, and the card says so.
    assert!(
        card.contains("Left in the dark") && card.contains("Carrying rights"),
        "the card names what the run could not carry: {card}"
    );

    // The verdict panel is still the proof, and still says PASS.
    assert!(card.contains("Independent verification — PASS"), "{card}");
    // And the growth loop closes: a stranger who read the story is offered the game.
    assert!(
        card.contains("href=\"/descent/play\""),
        "the card invites the reader to take their own light down: {card}"
    );
}

/// **The loss is legible.** A run abandoned one move from the exit banked NOTHING; its relics are
/// still in the pack. The card must not dress that as a haul: the cells paint `at-risk`, the words
/// say nothing is theirs, and no cell paints `banked`.
///
/// NON-VACUOUS: the crowned run above, with the SAME relics in the SAME columns, paints `banked`
/// and never paints `at-risk` — the difference is one `flee`.
#[tokio::test]
async fn an_unbanked_pack_never_looks_like_a_haul() {
    let (app, seed) = board();
    let abandoned = card_for(&app, &abandoned_record(&seed, "web:abandoned")).await;
    let crowned = card_for(&app, &crowned_record(&seed, "web:crowned")).await;

    assert!(
        abandoned.contains("rc-cell tag-relic at-risk"),
        "the carried relics are outlined, not filled: {abandoned}"
    );
    assert!(
        !abandoned.contains("rc-cell tag-vault banked"),
        "an unfinished run has banked NOTHING and no cell may say otherwise: {abandoned}"
    );
    assert!(
        abandoned.contains("still riding in the pack")
            && abandoned.contains("none of it is theirs"),
        "the risk is said in words, for the thumbnail and the screen reader: {abandoned}"
    );
    assert!(
        abandoned.contains("DELVING"),
        "the unfinished run is stamped unfinished: {abandoned}"
    );
    assert!(
        !abandoned.contains("CROWNED"),
        "an abandoned run is not dressed as a crowned one: {abandoned}"
    );

    // The differential: same columns, one `flee` apart.
    assert!(crowned.contains("rc-cell tag-vault banked"));
    assert!(!crowned.contains("rc-cell tag-relic at-risk"));
}

/// **The link unfurls.** A page whose whole job is to be posted is judged by its preview, and meta
/// tags are head-only — a card that emitted them from the body would preview as a bare URL.
#[tokio::test]
async fn the_share_link_carries_the_runs_story_into_a_social_preview() {
    let (app, seed) = board();
    let card = card_for(&app, &crowned_record(&seed, "web:crowned")).await;

    let head = card
        .split("</head>")
        .next()
        .expect("the document has a head");
    for tag in [
        "property=\"og:title\"",
        "property=\"og:description\"",
        "property=\"og:type\"",
        "name=\"twitter:card\"",
        "name=\"description\"",
    ] {
        assert!(head.contains(tag), "the head carries {tag}: {head}");
    }
    assert!(
        head.contains("CROWNED — web:crowned&#x27;s descent")
            || head.contains("CROWNED — web:crowned's descent"),
        "the preview TITLE leads with what happened: {head}"
    );
    assert!(
        head.contains("The Crown of the Deep came out of floor"),
        "the preview DESCRIPTION tells the story, not the schema: {head}"
    );
    assert!(
        head.contains("Re-verified by re-execution"),
        "the preview says the thing that makes the story worth believing: {head}"
    );
}

/// **The card is copyable as text** — the same board (`coordgrid_text`) the Discord embed and the
/// Telegram message paint, so a run pasted into a chat is the run and not a screenshot of one.
#[tokio::test]
async fn the_card_can_be_pasted_into_a_chat_as_the_same_board() {
    let (app, seed) = board();
    let card = card_for(&app, &crowned_record(&seed, "web:crowned")).await;

    assert!(card.contains("class=\"rc-text\""), "the copy block exists");
    let pre = card
        .split("<pre>")
        .nth(1)
        .and_then(|rest| rest.split("</pre>").next())
        .expect("the copy block holds a preformatted board");
    // Six rows: four floors, the pack, the vault — each with the caption that makes it mean
    // something without a manual.
    assert!(pre.contains("floor 1"), "{pre}");
    assert!(
        pre.contains("the run ended here"),
        "the text board says where it ended: {pre}"
    );
    assert!(
        pre.contains("banked —"),
        "the vault row is captioned: {pre}"
    );
    assert!(
        pre.contains('█') || pre.contains('░'),
        "the light clock rides along as the shared meter bar: {pre}"
    );
    assert!(
        pre.contains(&format!("of {BREATH}")),
        "against the game's own clock: {pre}"
    );
}

/// **The card and the live game are lit by ONE palette.**
///
/// The `/descent/play` redesign gave the game a meaning-bearing palette — brass is light, violet
/// is proof, rust is peril — and the run-card is the room a player is thrown into straight after
/// leaving it. A share link in the old cyan/mint tokens would read as a different product.
///
/// So this scrapes the SERVED play surface's own `--nd-*` colour tokens and requires the card's
/// `--rc-*` tokens of the same name to hold the identical hex. Retune the game and this fails
/// until the card follows; it cannot be satisfied by a copy that has since drifted.
#[tokio::test]
async fn the_card_is_lit_by_the_live_surfaces_palette() {
    let play = {
        let app = descent_play_router();
        let (status, body) = get(&app, "/descent/play").await;
        assert_eq!(status, StatusCode::OK, "the play shell serves");
        body
    };
    let (app, seed) = board();
    let card = card_for(&app, &crowned_record(&seed, "web:crowned")).await;

    // `--nd-torch-hot:#f0c98d` → ("torch-hot", "#f0c98d")
    let mut checked = 0;
    for chunk in play.split("--nd-").skip(1) {
        let Some((name, rest)) = chunk.split_once(':') else {
            continue;
        };
        if !rest.starts_with('#') {
            continue; // not a colour token (a number, a var(), an easing curve)
        }
        let hex: String = rest[..]
            .chars()
            .take_while(|c| c.is_ascii_hexdigit() || *c == '#')
            .collect();
        if hex.len() < 4 {
            continue;
        }
        let mine = format!("--rc-{name}:{hex}");
        // Only names the card actually uses are welded; the card need not adopt every token.
        if !card.contains(&format!("--rc-{name}:")) {
            continue;
        }
        assert!(
            card.contains(&mine),
            "the run-card's `--rc-{name}` must be the play surface's `--nd-{name}` ({hex}) — the \
             share link is the room the player just left, and a drifted token makes it a \
             different product"
        );
        checked += 1;
    }
    assert!(
        checked >= 12,
        "the palette weld covered only {checked} tokens — if this collapses it is passing \
         vacuously, not agreeing"
    );

    // The three meanings, pinned where they actually land on the board: banked custody is PROOF
    // (violet), a carried relic is LIGHT (brass). If those two ever paint the same, the card has
    // stopped telling the story it exists to tell.
    assert!(
        card.contains("rc-cell tag-vault banked"),
        "banked custody paints as proof: {card}"
    );
    assert!(
        card.contains(".rc-cell.tag-vault{color:var(--rc-proof-lit)")
            && card.contains(".rc-cell.tag-relic{color:var(--rc-torch)"),
        "violet is proof and brass is light — not the other way round: {card}"
    );
}

/// **The card and the live game speak ONE alphabet.** `native_descent`'s glyph table is private, so
/// the card mirrors it — and this is the weld that keeps the mirror honest: every `const GLYPH_* =
/// "…"` the SERVED play controller declares must appear in the card's own legend. Change a glyph on
/// either surface and this fails until they agree again.
#[tokio::test]
async fn the_card_and_the_live_surface_speak_one_alphabet() {
    // The play controller's OWN router, not the whole product app: this test needs one static
    // asset, and `make_app` additionally arms the catalog's PQ identity layer (which fail-closes
    // hard, and correctly, when the linked Lean archive does not export the verified cores).
    let js = {
        let app = descent_play_router();
        let (status, body) = get(&app, "/descent/play/static/app.js").await;
        assert_eq!(status, StatusCode::OK, "the play controller serves");
        body
    };
    let (app, seed) = board();
    let card = card_for(&app, &crowned_record(&seed, "web:crowned")).await;
    let legend = card
        .split("class=\"rc-legend\">")
        .nth(1)
        .and_then(|rest| rest.split("</p>").next())
        .expect("the card carries a legend")
        .to_string();

    // Scrape the live surface's OWN declarations rather than restating them here — a test that
    // hard-codes the alphabet cannot notice the game changing it.
    let mut found = 0;
    for line in js.lines() {
        let line = line.trim();
        let Some(rest) = line.strip_prefix("const GLYPH_") else {
            continue;
        };
        let Some((name, value)) = rest.split_once(" = ") else {
            continue;
        };
        let glyph = value.trim_end_matches(';').trim_matches('"');
        assert!(!glyph.is_empty(), "GLYPH_{name} declares a glyph");
        found += 1;
        // `>` is escaped in HTML; compare against the escaped form when that is what it becomes.
        let escaped = glyph.replace('&', "&amp;").replace('>', "&gt;");
        assert!(
            legend.contains(glyph) || legend.contains(&escaped),
            "the run-card's legend carries GLYPH_{name} (`{glyph}`) — the live surface draws it, \
             so a stranger who plays and then shares must see ONE alphabet. Legend: {legend}"
        );
    }
    assert!(
        found >= 10,
        "the play controller declares the whole glyph table ({found} found) — if this collapses, \
         the weld above is passing vacuously"
    );
}
