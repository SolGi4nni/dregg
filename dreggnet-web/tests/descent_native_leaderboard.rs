//! Exact compatibility weld from the browser-native portable record to the Descent board.
//!
//! The existing `/descent/submit` endpoint consumes procgen passage-choice indices. The browser
//! runs the Lean-native game and emits `{turn,arg}` events plus exact receipts/states/roots; those
//! semantics are intentionally not interchangeable. These tests pin the honest boundary: the old
//! endpoint refuses the native shape, while `/descent/native/submit` replays the full native record,
//! emits a share card, and ranks only crowned native settlements in a separate lane.

use std::sync::Arc;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dregg_node_target::{NodeTarget, StubNode};
use dreggnet_offerings::native_descent::{
    MAX_NATIVE_DESCENT_EVENTS, NativeDescentMove, NativeDescentOffering, NativeDescentRecord,
};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};
use dreggnet_web::descent_store::{
    DescentRunStore, InMemoryDescentRunStore, SqliteDescentRunStore, StoredDay,
};
use dreggnet_web::{DescentState, descent_router};
use dungeon_on_dregg::descent::Sim;
use procgen_dregg::{CommittedSeed, daily_seed};
use tower::ServiceExt;

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

fn normalized_native_seed(seed: &CommittedSeed) -> u8 {
    ((u64::from(native_seed_input(seed)) % 251) + 1) as u8
}

fn land(
    offering: &NativeDescentOffering,
    session: &mut dreggnet_offerings::native_descent::NativeDescentSession,
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
        Outcome::Refused(reason) => panic!("native test move {turn}({arg}) refused: {reason}"),
    }
}

fn crowned_record(seed: &CommittedSeed, actor: &str) -> NativeDescentRecord {
    let offering = NativeDescentOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(u64::from(native_seed_input(seed))))
        .expect("native day opens");
    for (turn, arg) in [
        ("delve", 0),
        ("smite", 0),
        ("loot", 1),
        ("unlock", 2),
        ("delve", 0),
        ("smite", 0),
        ("loot", 2),
        ("unlock", 3),
        ("delve", 0),
        ("smite", 0),
        ("smite", 0),
        ("loot", 3),
        ("unlock", 4),
        ("delve", 0),
        ("smite", 0),
        ("smite", 0),
        ("loot", 0),
        // ⚑ THE CLIMB HOME: `flee` is illegal below the surface, one light per floor.
        ("ascend", 0),
        ("ascend", 0),
        ("ascend", 0),
        ("ascend", 0),
        ("flee", 0),
    ] {
        land(&offering, &mut session, actor, turn, arg);
    }
    assert!(
        session
            .completion()
            .is_some_and(|completion| completion.crowned)
    );
    session.export_record()
}

fn settled_without_crown(seed: &CommittedSeed, actor: &str) -> NativeDescentRecord {
    let offering = NativeDescentOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(u64::from(native_seed_input(seed))))
        .expect("native day opens");
    land(&offering, &mut session, actor, "flee", 0);
    assert!(
        session
            .completion()
            .is_some_and(|completion| !completion.crowned)
    );
    session.export_record()
}

fn exact_unsettled_prefix(seed: &CommittedSeed, actor: &str) -> NativeDescentRecord {
    let offering = NativeDescentOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(u64::from(native_seed_input(seed))))
        .expect("native day opens");
    land(&offering, &mut session, actor, "delve", 0);
    assert!(session.completion().is_none());
    session.export_record()
}

fn sim_wire(sim: &Sim) -> serde_json::Value {
    serde_json::json!({
        "depth": sim.depth,
        "spent": sim.spent,
        "wounds": sim.wounds,
        "fate": sim.fate,
        "ways": sim.ways,
        "custody": sim.custody,
        "pack": sim.pack(),
        "banked": sim.bank(),
    })
}

fn move_wire(command: NativeDescentMove) -> (&'static str, i64) {
    match command {
        NativeDescentMove::Delve => ("delve", 0),
        NativeDescentMove::Ascend => ("ascend", 0),
        NativeDescentMove::Unlock { way } => (
            "unlock",
            i64::try_from(way).expect("native way index fits the action wire"),
        ),
        NativeDescentMove::Smite => ("smite", 0),
        NativeDescentMove::Lunge => ("lunge", 0),
        NativeDescentMove::Loot { relic } => (
            "loot",
            i64::try_from(relic).expect("native relic index fits the action wire"),
        ),
        NativeDescentMove::Flee => ("flee", 0),
    }
}

/// Independent test-side encoding of the wasm portable schema. Duplicating this projection is
/// deliberate: an endpoint test must prove it accepts the browser's public shape, not call the
/// receiver's private conversion helper to manufacture a self-fulfilling fixture.
fn portable(record: &NativeDescentRecord) -> serde_json::Value {
    let events = record
        .events
        .iter()
        .map(|event| {
            let (turn, arg) = move_wire(event.command);
            serde_json::json!({
                "revision": event.revision,
                "actor": event.actor.as_str(),
                "turn": turn,
                "arg": arg,
                "receipt": event.receipt,
                "post": sim_wire(&event.post),
                "rootHex": hex(&event.root),
            })
        })
        .collect::<Vec<_>>();
    serde_json::json!({
        "format": "dregg.native-descent.record",
        "version": 3,
        "seed": record.seed,
        // v2 carries the run's provenance root, so the endpoint can re-execute a day-bound run
        // (the genesis root folds it in — a replay on the wrong root re-derives nothing).
        "daySeedHex": hex(record.day_seed.as_bytes()),
        "actor": record.actor.as_ref().map(|actor| actor.as_str()),
        "events": events,
        "rootHex": hex(&record.root),
        "checkpoint": record.checkpoint.as_ref().map(|checkpoint| serde_json::json!({
            "actor": checkpoint.actor.as_str(),
            "revision": checkpoint.revision,
            "rootHex": hex(&checkpoint.root),
            "state": sim_wire(&checkpoint.state),
        })),
        "completion": record.completion.as_ref().map(|completion| serde_json::json!({
            "actor": completion.actor.as_str(),
            "revision": completion.revision,
            "rootHex": hex(&completion.root),
            "settlementReceiptHashHex": hex(&completion.settlement_receipt_hash),
            "bankedRelics": completion.banked_relics,
            // v3: the banked relics' minted owned-notes cross the wire — the asset id is the
            // note's content-address (run day-seed, custody slot, player key) and the rarity is
            // its canonical committed tag byte.
            "bankedNotes": completion.banked_notes.iter().map(|note| serde_json::json!({
                "relic": note.relic,
                "assetIdHex": hex(&note.asset_id.bytes()),
                "rarity": note.rarity.tag(),
                "ownerHex": hex(&note.owner),
            })).collect::<Vec<_>>(),
            "crowned": completion.crowned,
        })),
    })
}

fn hex(bytes: &[u8; 32]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn temp_db(tag: &str) -> String {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir()
        .join(format!(
            "dreggnet-native-{tag}-{}-{nonce}.db",
            std::process::id()
        ))
        .to_string_lossy()
        .into_owned()
}

#[tokio::test]
async fn native_browser_record_replays_shares_and_ranks_only_in_its_own_lane() {
    let day_seed = daily_seed(&[91; 32]);
    let state = Arc::new(DescentState::new());
    state.open_day("native-day", day_seed);
    let app = descent_router(state);
    let native_record = crowned_record(&day_seed, "web:native-browser");
    // Offering-side ground truth for the banked-note payload the wire must carry faithfully.
    let minted = native_record
        .completion
        .as_ref()
        .expect("crowned run settled")
        .banked_notes
        .clone();
    assert_eq!(minted.len(), 4, "the crowned tape banked four relics");
    let record = portable(&native_record);

    // RED seam: the procgen endpoint requires `{player,moves:[choice_index]}` and must not silently
    // reinterpret the browser's verb/receipt record.
    let (old_status, old_body) = post(
        &app,
        "/descent/submit",
        serde_json::json!({ "day": "native-day", "record": record.clone() }),
    )
    .await;
    assert_eq!(old_status, StatusCode::UNPROCESSABLE_ENTITY, "{old_body}");

    // GREEN compatibility lane: exact native replay accepts the same public record.
    let (status, accepted) = post(
        &app,
        "/descent/native/submit",
        serde_json::json!({ "day": "native-day", "record": record }),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "{accepted}");
    assert_eq!(accepted["verified"], true, "{accepted}");
    assert_eq!(accepted["ranked"], true, "a crowned exit ranks: {accepted}");
    assert_eq!(accepted["kind"], "exact-native-replay");
    assert_eq!(accepted["banked_relics"], 4);

    // THE NOTES SURVIVED THE PROCESS BOUNDARY: the response carries the replayed (re-minted)
    // notes, and each content-address is byte-identical to the one the browser-side session
    // minted — not merely a count, and not an echo of the submission.
    let response_notes = accepted["banked_notes"]
        .as_array()
        .expect("v3 submit response carries the minted notes");
    assert_eq!(response_notes.len(), minted.len(), "{accepted}");
    for (wire, note) in response_notes.iter().zip(&minted) {
        assert_eq!(wire["relic"], serde_json::json!(note.relic));
        assert_eq!(
            wire["assetIdHex"],
            serde_json::json!(hex(&note.asset_id.bytes())),
            "the note's content-address crossed the wire unchanged"
        );
        assert_eq!(wire["rarity"], serde_json::json!(note.rarity.tag()));
        assert_eq!(wire["ownerHex"], serde_json::json!(hex(&note.owner)));
    }

    let share = accepted["share"].as_str().expect("native share path");
    let (card_status, card) = get(&app, share).await;
    assert_eq!(card_status, StatusCode::OK);
    assert!(card.contains("Independent verification — PASS"), "{card}");
    assert!(card.contains("CROWNED"), "{card}");
    assert!(card.contains("Minted notes"), "{card}");
    assert!(
        card.contains(&hex(&minted[0].asset_id.bytes())[..12]),
        "the run card shows the minted note's content-address: {card}"
    );
    assert!(
        card.contains("Lean-native compatibility artifact"),
        "{card}"
    );

    let (_, board) = get(&app, "/descent/leaderboard?day=native-day").await;
    assert!(board.contains("Lean-native browser ruleset"), "{board}");
    assert!(board.contains("web:native-browser"), "{board}");
    assert!(board.contains("verify native record"), "{board}");
}

#[tokio::test]
async fn native_submit_rejects_exact_envelope_tampering_and_a_wrong_day() {
    let day_seed = daily_seed(&[92; 32]);
    let state = Arc::new(DescentState::new());
    state.open_day("right-day", day_seed);

    let other_seed = (0u8..=u8::MAX)
        .map(|byte| daily_seed(&[byte; 32]))
        .find(|seed| normalized_native_seed(seed) != normalized_native_seed(&day_seed))
        .expect("some committed day has a different normalized native seed");
    state.open_day("wrong-day", other_seed);
    let app = descent_router(state);
    let record = portable(&crowned_record(&day_seed, "web:honest"));

    let mut forged = record.clone();
    forged["events"][0]["rootHex"] = serde_json::json!("00".repeat(32));
    let (status, refused) = post(
        &app,
        "/descent/native/submit",
        serde_json::json!({ "day": "right-day", "record": forged }),
    )
    .await;
    assert_eq!(status, StatusCode::BAD_REQUEST, "{refused}");
    assert_eq!(refused["verified"], false);
    assert_eq!(refused["ranked"], false);
    assert!(
        refused["error"]
            .as_str()
            .is_some_and(|error| error.contains("differs from exact")),
        "{refused}"
    );

    let mut substituted_actor = record.clone();
    substituted_actor["events"][1]["actor"] = serde_json::json!("web:intruder");
    let (status, substituted) = post(
        &app,
        "/descent/native/submit",
        serde_json::json!({ "day": "right-day", "record": substituted_actor }),
    )
    .await;
    assert_eq!(status, StatusCode::BAD_REQUEST, "{substituted}");
    assert!(
        substituted["error"]
            .as_str()
            .is_some_and(|error| error.contains("refused on replay")),
        "{substituted}"
    );

    let mut wrong_version = record.clone();
    wrong_version["version"] = serde_json::json!(2);
    let (status, version_refused) = post(
        &app,
        "/descent/native/submit",
        serde_json::json!({ "day": "right-day", "record": wrong_version }),
    )
    .await;
    assert_eq!(status, StatusCode::BAD_REQUEST, "{version_refused}");
    assert!(
        version_refused["error"]
            .as_str()
            .is_some_and(|error| error.contains("unsupported native Descent record version 2")),
        "{version_refused}"
    );

    let mut unknown_field = record.clone();
    unknown_field["untrustedSummary"] = serde_json::json!(true);
    let (status, schema_refused) = post(
        &app,
        "/descent/native/submit",
        serde_json::json!({ "day": "right-day", "record": unknown_field }),
    )
    .await;
    assert_eq!(status, StatusCode::BAD_REQUEST, "{schema_refused}");
    assert!(
        schema_refused["error"]
            .as_str()
            .is_some_and(|error| error.contains("unknown field")),
        "{schema_refused}"
    );

    // A legitimate portable-record route advertises the wasm boundary's 8 MiB cap, not axum's
    // default 2 MiB JSON cap. Cross that default with a hostile unknown field: the request must
    // reach our strict record schema and fail there, proving the route-specific limit is wired.
    let mut over_default_limit = record.clone();
    over_default_limit["padding"] = serde_json::json!("x".repeat(3 * 1024 * 1024));
    let (status, large_schema_refused) = post(
        &app,
        "/descent/native/submit",
        serde_json::json!({ "day": "right-day", "record": over_default_limit }),
    )
    .await;
    assert_eq!(status, StatusCode::BAD_REQUEST, "{large_schema_refused}");
    assert!(
        large_schema_refused["error"]
            .as_str()
            .is_some_and(|error| error.contains("unknown field")),
        "the request should reach the native schema, not axum's 2 MiB default: {large_schema_refused}"
    );

    // The persisted/browser wire uses u64 indices even while a native implementation may use
    // platform-sized indices internally. A hostile wide index must parse portably and then lose the
    // exact-replay comparison, not overflow/deserialization-fail at the compatibility boundary.
    let mut wide_relic_index = record.clone();
    wide_relic_index["completion"]["bankedRelics"][0] = serde_json::json!(u64::from(u32::MAX) + 1);
    let (status, wide_refused) = post(
        &app,
        "/descent/native/submit",
        serde_json::json!({ "day": "right-day", "record": wide_relic_index }),
    )
    .await;
    assert_eq!(status, StatusCode::BAD_REQUEST, "{wide_refused}");
    assert!(
        wide_refused["error"]
            .as_str()
            .is_some_and(|error| error.contains("differs from exact")),
        "wide wire index should parse before exact comparison: {wide_refused}"
    );

    let mut too_many_events = record.clone();
    let first_event = too_many_events["events"][0].clone();
    too_many_events["events"] =
        serde_json::Value::Array(vec![first_event; MAX_NATIVE_DESCENT_EVENTS + 1]);
    let (status, bounded) = post(
        &app,
        "/descent/native/submit",
        serde_json::json!({ "day": "right-day", "record": too_many_events }),
    )
    .await;
    assert_eq!(status, StatusCode::BAD_REQUEST, "{bounded}");
    assert!(
        bounded["error"]
            .as_str()
            .is_some_and(|error| error.contains("exceeds the native Descent bound")),
        "{bounded}"
    );

    let (status, wrong_day) = post(
        &app,
        "/descent/native/submit",
        serde_json::json!({ "day": "wrong-day", "record": record }),
    )
    .await;
    assert_eq!(status, StatusCode::BAD_REQUEST, "{wrong_day}");
    assert!(
        wrong_day["error"]
            .as_str()
            .is_some_and(|error| error.contains("does not belong to this day")),
        "{wrong_day}"
    );
}

/// A tampered or forged banked-NOTE payload is refused BY NAME — never accepted, and never an
/// anonymous whole-envelope mismatch. The note's asset id content-addresses (run day-seed,
/// custody slot, player key), so replay re-mints it and any substitution fails to re-derive.
#[tokio::test]
async fn a_forged_banked_note_payload_is_refused_by_name() {
    let day_seed = daily_seed(&[97; 32]);
    let state = Arc::new(DescentState::new());
    state.open_day("note-day", day_seed);
    let app = descent_router(state);
    let record = portable(&crowned_record(&day_seed, "web:honest-notes"));

    async fn refused_with(
        app: &axum::Router,
        record: serde_json::Value,
        named: &str,
    ) -> serde_json::Value {
        let (status, refused) = post(
            app,
            "/descent/native/submit",
            serde_json::json!({ "day": "note-day", "record": record }),
        )
        .await;
        assert_eq!(status, StatusCode::BAD_REQUEST, "{refused}");
        assert_eq!(refused["verified"], false, "{refused}");
        assert!(
            refused["error"]
                .as_str()
                .is_some_and(|error| error.contains(named)),
            "expected a refusal naming {named:?}: {refused}"
        );
        refused
    }

    // A substituted content-address: structurally valid hex that does not re-mint.
    let mut forged_id = record.clone();
    forged_id["completion"]["bankedNotes"][0]["assetIdHex"] = serde_json::json!("11".repeat(32));
    refused_with(&app, forged_id, "banked notes do not re-mint").await;

    // An inflated tier under a non-canonical tag byte fails closed at decode, by name.
    let mut fake_tier = record.clone();
    fake_tier["completion"]["bankedNotes"][0]["rarity"] = serde_json::json!(9);
    refused_with(&app, fake_tier, "rarity tag 9 is not canonical").await;

    // A canonical-but-wrong tier is caught by the re-mint, not believed.
    let honest_tag = record["completion"]["bankedNotes"][0]["rarity"]
        .as_u64()
        .expect("wire tag");
    let mut relabeled = record.clone();
    relabeled["completion"]["bankedNotes"][0]["rarity"] = serde_json::json!((honest_tag + 1) % 4);
    refused_with(&app, relabeled, "banked notes do not re-mint").await;

    // A stolen note: the same run claiming a different owner key.
    let mut stolen = record.clone();
    stolen["completion"]["bankedNotes"][0]["ownerHex"] = serde_json::json!("22".repeat(32));
    refused_with(&app, stolen, "banked notes do not re-mint").await;

    // A dropped-notes (v2-shaped) completion no longer decodes: the field is load-bearing.
    let mut dropped = record.clone();
    dropped["completion"]
        .as_object_mut()
        .expect("completion object")
        .remove("bankedNotes");
    refused_with(&app, dropped, "bankedNotes").await;

    // The honest record still lands after all the refusals (nothing was retained for them).
    let (status, accepted) = post(
        &app,
        "/descent/native/submit",
        serde_json::json!({ "day": "note-day", "record": record }),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "{accepted}");
    assert_eq!(accepted["verified"], true, "{accepted}");
}

#[tokio::test]
async fn exact_non_crowned_native_settlement_is_shareable_but_never_ranked() {
    let day_seed = daily_seed(&[93; 32]);
    let state = Arc::new(DescentState::new());
    state.open_day("turn-back-day", day_seed);
    let app = descent_router(state);

    let prefix = portable(&exact_unsettled_prefix(&day_seed, "web:unfinished"));
    let (prefix_status, prefix_refused) = post(
        &app,
        "/descent/native/submit",
        serde_json::json!({ "day": "turn-back-day", "record": prefix }),
    )
    .await;
    assert_eq!(prefix_status, StatusCode::BAD_REQUEST, "{prefix_refused}");
    assert!(
        prefix_refused["error"]
            .as_str()
            .is_some_and(|error| error.contains("no terminal flee settlement")),
        "{prefix_refused}"
    );

    let record = portable(&settled_without_crown(&day_seed, "web:turn-back"));

    let (status, accepted) = post(
        &app,
        "/descent/native/submit",
        serde_json::json!({ "day": "turn-back-day", "record": record }),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "{accepted}");
    assert_eq!(accepted["verified"], true);
    assert_eq!(accepted["ranked"], false);
    assert_eq!(
        accepted["banked_notes"],
        serde_json::json!([]),
        "a run that banked nothing minted nothing — and is otherwise unchanged: {accepted}"
    );
    let share = accepted["share"].as_str().expect("verified run card");
    let (_, card) = get(&app, share).await;
    assert!(card.contains("Independent verification — PASS"), "{card}");
    assert!(card.contains("not crowned and not ranked"), "{card}");

    let (_, board) = get(&app, "/descent/leaderboard?day=turn-back-day").await;
    assert!(
        !board.contains("web:turn-back"),
        "non-crowned run ranked: {board}"
    );
}

#[tokio::test]
async fn persisted_native_artifact_survives_restart_only_after_boot_replay() {
    let day_seed = daily_seed(&[94; 32]);
    let store = Arc::new(InMemoryDescentRunStore::new());
    let first = Arc::new(DescentState::with_store(store.clone()));
    first.open_day("durable-native-day", day_seed);
    let first_app = descent_router(first);
    let record = portable(&crowned_record(&day_seed, "web:durable"));
    let (status, accepted) = post(
        &first_app,
        "/descent/native/submit",
        serde_json::json!({ "day": "durable-native-day", "record": record }),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "{accepted}");
    assert_eq!(accepted["durable"], true, "{accepted}");
    let share = accepted["share"].as_str().unwrap().to_string();

    // A fresh state owns no in-memory run. `load_from_store` regenerates the day and independently
    // replays the full native record before restoring its card/board presence.
    let restarted = Arc::new(DescentState::with_store(store));
    restarted.load_from_store();
    let restarted_app = descent_router(restarted);
    let (card_status, card) = get(&restarted_app, &share).await;
    assert_eq!(card_status, StatusCode::OK);
    assert!(card.contains("Independent verification — PASS"), "{card}");
    let (_, board) = get(
        &restarted_app,
        "/descent/leaderboard?day=durable-native-day",
    )
    .await;
    assert!(board.contains("web:durable"), "{board}");
}

#[tokio::test]
async fn sqlite_restart_drops_a_tampered_native_record_instead_of_resurrecting_it() {
    let day_seed = daily_seed(&[95; 32]);
    let db_path = temp_db("tampered-restart");
    let share = {
        let store = Arc::new(SqliteDescentRunStore::open(&db_path).expect("sqlite opens"));
        let state = Arc::new(DescentState::with_store(store));
        state.open_day("hostile-restart-day", day_seed);
        let app = descent_router(state);
        let record = portable(&crowned_record(&day_seed, "web:must-not-resurrect"));
        let (status, accepted) = post(
            &app,
            "/descent/native/submit",
            serde_json::json!({ "day": "hostile-restart-day", "record": record }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "{accepted}");
        assert_eq!(accepted["durable"], true, "{accepted}");
        accepted["share"].as_str().unwrap().to_string()
    };

    // Hostile-at-rest edit: retain the original content-derived row key but alter one journal root.
    // Boot must not trust either the row key or the once-successful submission verdict.
    let conn = rusqlite::Connection::open(&db_path).expect("open persisted board for tamper");
    let record_json: String = conn
        .query_row(
            "SELECT record_json FROM descent_native_runs LIMIT 1",
            [],
            |row| row.get(0),
        )
        .expect("native row exists");
    let mut tampered: serde_json::Value = serde_json::from_str(&record_json).unwrap();
    tampered["events"][0]["rootHex"] = serde_json::json!("00".repeat(32));
    conn.execute(
        "UPDATE descent_native_runs SET record_json = ?1",
        [tampered.to_string()],
    )
    .expect("tamper row");
    drop(conn);

    let restarted_store = Arc::new(SqliteDescentRunStore::open(&db_path).expect("reopen sqlite"));
    let restarted = Arc::new(DescentState::with_store(restarted_store));
    restarted.load_from_store();
    let app = descent_router(restarted);
    let (_, card) = get(&app, &share).await;
    assert!(
        card.contains("No such run"),
        "tampered artifact restored: {card}"
    );
    assert!(
        !card.contains("Independent verification — PASS"),
        "tampered artifact received a stale PASS: {card}"
    );
    let (_, board) = get(&app, "/descent/leaderboard?day=hostile-restart-day").await;
    assert!(
        !board.contains("class=\"player\">web:must-not-resurrect<"),
        "tampered artifact ranked after restart: {board}"
    );

    drop(app);
    let _ = std::fs::remove_file(&db_path);
}

/// ⚑ THE CANARY, driven end-to-end: a native run PLAYED TO COMPLETION auto-anchors — it ranks on
/// the day's leaderboard AND lands on the devnet node's ledger — without a separate procgen-style
/// submit. The browser fires this same POST on the terminal settlement; here the completed record
/// is submitted directly to the same endpoint against a `Federation` StubNode, so the whole
/// play -> rank -> anchor chain is exercised in-process.
///
/// The commitment the lane anchors is the run's terminal journal head (the un-retconnable tip of
/// the actor-bound hash chain the record attests), taken verbatim as the node's turn id by the
/// modeled stub — so `stub.contains(root)` is the on-ledger membership proof, not a stored flag.
#[tokio::test]
async fn native_crowned_completion_auto_anchors_on_the_node_and_ranks() {
    let day_seed = daily_seed(&[120; 32]);
    let stub: Arc<StubNode> = StubNode::new();
    let target = NodeTarget::federation(stub.clone());
    let state = Arc::new(DescentState::new().with_node_target(target));
    assert!(state.settles_to_a_node(), "Federation target opted in");
    state.open_day("anchor-day", day_seed);
    let app = descent_router(state);

    let native_record = crowned_record(&day_seed, "web:auto-anchor");
    let completion_root = native_record
        .completion
        .as_ref()
        .expect("crowned run settled")
        .root;
    let record = portable(&native_record);

    // The node is untouched until the run completes and is submitted.
    assert!(stub.is_empty(), "node touched before any run submitted");

    let (status, accepted) = post(
        &app,
        "/descent/native/submit",
        serde_json::json!({ "day": "anchor-day", "record": record }),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "{accepted}");
    assert_eq!(accepted["verified"], true, "{accepted}");
    assert_eq!(accepted["ranked"], true, "a crowned exit ranks: {accepted}");

    // ANCHORED: the native lane settled the run onto the node, exactly as the procgen lane does.
    assert_eq!(
        accepted["settled"], true,
        "crowned run anchored: {accepted}"
    );
    assert_eq!(
        accepted["node_turn_hash"],
        serde_json::json!(hex(&completion_root)),
        "the anchored commitment is the run's terminal journal head: {accepted}"
    );
    // The on-ledger membership proof — the commitment is present on the node's finalized log.
    assert!(
        stub.contains(&completion_root),
        "the run's terminal journal head is on the node's finalized log"
    );
    assert_eq!(stub.len(), 1, "exactly one turn anchored");

    // RANKED + REPLAY-VERIFIABLE: the run appears on the day's leaderboard and its share card
    // re-verifies by fresh replay.
    let (_, board) = get(&app, "/descent/leaderboard?day=anchor-day").await;
    assert!(
        board.contains("web:auto-anchor"),
        "run ranks on the board: {board}"
    );
    let share = accepted["share"].as_str().expect("native share path");
    let (card_status, card) = get(&app, share).await;
    assert_eq!(card_status, StatusCode::OK);
    assert!(card.contains("Independent verification — PASS"), "{card}");
    assert!(card.contains("CROWNED"), "{card}");
}

/// A non-crowned settlement is shareable but does not rank — and therefore does NOT touch the node
/// (the anchor is the crowned/ranked leg only, mirroring the procgen lane's "only a ranked run
/// settles").
#[tokio::test]
async fn native_non_crowned_settlement_does_not_anchor_the_node() {
    let day_seed = daily_seed(&[121; 32]);
    let stub: Arc<StubNode> = StubNode::new();
    let target = NodeTarget::federation(stub.clone());
    let state = Arc::new(DescentState::new().with_node_target(target));
    state.open_day("no-crown-day", day_seed);
    let app = descent_router(state);

    let record = portable(&settled_without_crown(&day_seed, "web:turned-back"));
    let (status, accepted) = post(
        &app,
        "/descent/native/submit",
        serde_json::json!({ "day": "no-crown-day", "record": record }),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "{accepted}");
    assert_eq!(accepted["verified"], true, "{accepted}");
    assert_eq!(accepted["ranked"], false, "not crowned: {accepted}");
    // No anchor for a non-ranked run.
    assert!(
        accepted.get("settled").is_none(),
        "non-crowned run must not anchor: {accepted}"
    );
    assert!(
        stub.is_empty(),
        "the node was never touched for a non-crowned run"
    );
}

/// NO-CHEAT, at the node boundary: a forged native record is refused by the exact-replay gate
/// before it can rank, so the node is NEVER touched for a cheat — unchanged from the board's
/// existing fail-closed semantics, now also true of the anchor leg.
#[tokio::test]
async fn a_forged_native_record_never_reaches_the_node() {
    let day_seed = daily_seed(&[122; 32]);
    let stub: Arc<StubNode> = StubNode::new();
    let target = NodeTarget::federation(stub.clone());
    let state = Arc::new(DescentState::new().with_node_target(target));
    state.open_day("forge-day", day_seed);
    let app = descent_router(state);

    let mut forged = portable(&crowned_record(&day_seed, "web:forger"));
    forged["events"][0]["rootHex"] = serde_json::json!("00".repeat(32));
    let (status, refused) = post(
        &app,
        "/descent/native/submit",
        serde_json::json!({ "day": "forge-day", "record": forged }),
    )
    .await;
    assert_eq!(status, StatusCode::BAD_REQUEST, "{refused}");
    assert_eq!(refused["verified"], false, "{refused}");
    assert_eq!(refused["ranked"], false, "{refused}");
    assert!(stub.is_empty(), "a forged run must never touch the node");

    // And it does not appear on the leaderboard.
    let (_, board) = get(&app, "/descent/leaderboard?day=forge-day").await;
    assert!(!board.contains("web:forger"), "forged run ranked: {board}");
}

/// The default `Local` target keeps the native lane in-process: a crowned run still ranks, but the
/// response carries NO `settled` field and `settle_native_run` is an `Ok(None)` no-op — so the
/// committed suite + node-free demo are byte-identical (the non-vacuity control for the anchor).
#[tokio::test]
async fn local_native_submit_ranks_but_does_not_anchor() {
    let day_seed = daily_seed(&[123; 32]);
    let state = Arc::new(DescentState::new()); // NodeTarget::Local by default
    assert!(!state.settles_to_a_node(), "Local is the default");
    state.open_day("local-day", day_seed);

    let record = portable(&crowned_record(&day_seed, "web:local"));
    let app = descent_router(state.clone());
    let (status, accepted) = post(
        &app,
        "/descent/native/submit",
        serde_json::json!({ "day": "local-day", "record": record }),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "{accepted}");
    assert_eq!(accepted["ranked"], true, "{accepted}");
    assert!(
        accepted.get("settled").is_none(),
        "Local mode adds no anchor field: {accepted}"
    );

    // The method is a direct Ok(None) no-op — nothing leaves the process.
    let run_id = accepted["run_id"].as_str().expect("run id").to_string();
    let landed = state
        .settle_native_run("local-day", &run_id)
        .expect("Local native settle never errors");
    assert!(
        landed.is_none(),
        "Local mode keeps the native run in-process"
    );
}

#[tokio::test]
async fn conflicting_persisted_day_key_never_claims_a_durable_native_artifact() {
    let played_seed = daily_seed(&[96; 32]);
    let stored_seed = (0u8..=u8::MAX)
        .map(|byte| daily_seed(&[byte; 32]))
        .find(|seed| normalized_native_seed(seed) != normalized_native_seed(&played_seed))
        .expect("some committed day has a distinct native seed");
    let store = Arc::new(InMemoryDescentRunStore::new());
    store
        .persist_day(&StoredDay {
            key: "conflicting-day".to_string(),
            seed_hex: hex(stored_seed.as_bytes()),
        })
        .unwrap();

    // Simulate a caller that skipped boot load and opened a conflicting world under an already
    // persisted key. The in-memory exact replay may pass, but INSERT-OR-IGNORE cannot replace the
    // old day. The response must expose that the artifact did not become restart-durable.
    let state = Arc::new(DescentState::with_store(store.clone()));
    state.open_day("conflicting-day", played_seed);
    let app = descent_router(state);
    let record = portable(&crowned_record(&played_seed, "web:ephemeral-conflict"));
    let (status, accepted) = post(
        &app,
        "/descent/native/submit",
        serde_json::json!({ "day": "conflicting-day", "record": record }),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "{accepted}");
    assert_eq!(accepted["verified"], true, "{accepted}");
    assert_eq!(accepted["durable"], false, "{accepted}");
    let share = accepted["share"].as_str().unwrap().to_string();
    drop(app);

    let restarted = Arc::new(DescentState::with_store(store));
    restarted.load_from_store();
    let restarted_app = descent_router(restarted);
    let (_, card) = get(&restarted_app, &share).await;
    assert!(
        card.contains("No such run"),
        "non-durable conflict resurrected after restart: {card}"
    );
}
