//! Native linked probe for the Lean-owned Path of Angels station daily read.
//!
//! It calls the real linked symbol and asserts what the served document IS and, more importantly,
//! what it is NOT.
//!
//! # The read is honest before any crate is opened
//!
//! The panel this read serves is `ShipInstrumentPanel.initial` — every gauge at its installed
//! value — and that is not a placeholder: no `ShipInstrumentPanel.Receipt` can be produced without
//! an accepted `SalvageCrate.OpenReceipt`, and no accepted opening can be produced without a
//! `CurrentStateCapability`, which is `opaque` with no producer anywhere in the tree. The write
//! path is absent BY TYPE. This probe pins `observed`/`admitted` at zero so the day that changes,
//! it changes visibly.
//!
//! # What must never appear
//!
//! No run seed, slot secret, commitment or target. That containment is structural rather than a
//! filter — `HiddenInstance` and `SlotDeriveRuntime` are not in `StationDailyRuntime`'s import
//! cone, so those values do not exist to leak — but the assertion is here because a future import
//! would make them reachable silently.
//!
//! No per-player field in the communal half. `ShipInstrumentPanel.State` has no such field, and
//! `the_served_panel_does_not_depend_on_the_crew` proves substituting any request leaves the
//! communal fields bit-identical. This probe checks that on the EMITTED BYTES of two real calls,
//! which is an independent source from the Lean theorem: the theorem is about the projection, this
//! is about what the linked archive actually returned.
#![cfg(feature = "lean-lib")]

use dregg_lean_ffi::poa_station_daily_ffi::{
    poa_station_daily_read_available, read_poa_station_daily, station_daily_request,
    PoaStationDailyVerdict,
};
use serde_json::Value;

/// The authored officer on the crate's eligible roster: `SalvageCrateExamples.digest 40`.
const OFFICER_KEY: &str = "2828282828282828282828282828282828282828282828282828282828282828";

fn read(request: &str) -> PoaStationDailyVerdict {
    read_poa_station_daily(request).expect("linked Lean station read must be callable")
}

fn document(request: &str) -> (String, Value) {
    let PoaStationDailyVerdict::Read(view) = read(request) else {
        panic!("Lean refused the canonical station request: {request}");
    };
    assert!(
        view.was_read_for(request.as_bytes()),
        "the carrier must be bound to this exact request"
    );
    let bytes = view.into_string();
    let parsed: Value = serde_json::from_str(&bytes).expect("the station document is JSON");
    (bytes, parsed)
}

#[test]
fn the_communal_panel_is_the_installed_ship_and_names_nobody() {
    assert!(
        poa_station_daily_read_available(),
        "dregg_poa_station_daily_read is absent or initialization failed; this is refusal, not skip"
    );

    let (bytes, view) = document(&station_daily_request(None));

    assert_eq!(view["format"], "POA-STATION-DAILY-OUT-1");
    assert_eq!(
        view["crew"],
        Value::Null,
        "the panel route must name no crew member"
    );

    // The installed ship: gauges present and readable, and nothing has moved them.
    let gauges = view["gauges"].as_array().expect("the panel has gauges");
    assert!(!gauges.is_empty(), "a panel with no dial is not a panel");
    for gauge in gauges {
        assert_eq!(gauge["exact_total"], 0, "no opening has been folded in");
        assert_eq!(gauge["shown"], 0);
        assert_eq!(gauge["at_full"], false);
        // `exact_total` is the unclipped arithmetic and `shown` is the needle. Both are
        // published so the display scale can never quietly become the bound.
        assert!(
            gauge["full_at"].as_u64().expect("a display scale") > 0,
            "a gauge whose scale is zero is at full before anything happens"
        );
    }
    assert_eq!(view["observed"], 0);
    assert_eq!(view["admitted"], 0);
    assert_eq!(view["recovered_kinds"], 0);

    // The crate the panel belongs to is real content, not an empty shell.
    assert!(view["table_rows"].as_u64().expect("authored rows") > 0);
    assert!(view["ticket_count"].as_u64().expect("authored tickets") > 0);

    for forbidden in [
        "run_seed",
        "runSeed",
        "target",
        "secret",
        "commitment",
        "slot",
        "transcript",
    ] {
        assert!(
            !bytes.contains(forbidden),
            "the station document must never carry `{forbidden}`: {bytes}"
        );
    }
    // No attendance vocabulary either. The panel proves it keeps no such state; this fails if a
    // future field starts implying it does.
    for forbidden in ["streak", "last_seen", "attendance", "player", "leaderboard"] {
        assert!(
            !bytes.contains(forbidden),
            "the station document must never carry `{forbidden}`: {bytes}"
        );
    }
}

#[test]
fn naming_a_crew_member_adds_a_rotation_and_moves_no_gauge() {
    assert!(
        poa_station_daily_read_available(),
        "dregg_poa_station_daily_read is absent or initialization failed; this is refusal, not skip"
    );

    let (anonymous_bytes, anonymous) = document(&station_daily_request(None));
    let (crew_bytes, crew) = document(&station_daily_request(Some(OFFICER_KEY)));

    // ⚑ The communal half, on the EMITTED BYTES of two real calls into the linked archive.
    for field in [
        "gauges",
        "observed",
        "admitted",
        "recovered_kinds",
        "federation_id",
        "content_session",
        "content_epoch",
        "opens_at",
        "closes_at",
        "table_rows",
        "ticket_count",
    ] {
        assert_eq!(
            anonymous[field], crew[field],
            "naming a crew member changed the communal field `{field}`"
        );
    }

    // Erasing `crew` from the named document yields the anonymous one exactly.
    let mut erased = crew.clone();
    erased["crew"] = Value::Null;
    assert_eq!(
        erased, anonymous,
        "the two documents must differ only in `crew`"
    );

    let member = &crew["crew"];
    assert_eq!(member["key"], OFFICER_KEY);
    assert_eq!(
        member["eligible"], true,
        "the authored officer is on the curator's roster"
    );

    // The visible rotation: one entry per authored beacon, each naming its period and beacon.
    let rotation = member["rotation"]
        .as_array()
        .expect("a named crew member has a rotation");
    assert!(!rotation.is_empty(), "the authored schedule is not empty");
    let mut periods: Vec<u64> = Vec::new();
    for slot in rotation {
        let period = slot["period"].as_u64().expect("an authored period");
        assert!(
            periods.last().is_none_or(|previous| *previous < period),
            "the beacon schedule is strictly ordered"
        );
        periods.push(period);
        let beacon = slot["beacon"].as_str().expect("an authored beacon");
        assert_eq!(beacon.len(), 64, "a beacon is a 32-byte digest in hex");
    }

    assert!(
        !crew_bytes.contains("run_seed") && !crew_bytes.contains("secret"),
        "the crew document must never carry a hidden instance: {crew_bytes}"
    );
    assert!(!anonymous_bytes.contains("rotation"));
}

#[test]
fn an_ineligible_crew_key_is_told_so_rather_than_refused() {
    assert!(
        poa_station_daily_read_available(),
        "dregg_poa_station_daily_read is absent or initialization failed; this is refusal, not skip"
    );

    let stranger = "ff".repeat(32);
    let (_, view) = document(&station_daily_request(Some(&stranger)));
    assert_eq!(view["crew"]["key"], stranger);
    assert_eq!(
        view["crew"]["eligible"], false,
        "a key that is not on the authored roster is not eligible"
    );
}

/// The canonical seal is a BYTE comparison: Lean re-encodes what it parsed and refuses anything
/// that is not the exact image its own encoder emits. Each of these is one real way a caller
/// drifts, and every one must be the empty refusal sentinel rather than a served document.
#[test]
fn every_uncanonical_request_is_refused() {
    assert!(
        poa_station_daily_read_available(),
        "dregg_poa_station_daily_read is absent or initialization failed; this is refusal, not skip"
    );

    for hostile in [
        // An extra field — the shape a smuggled streak or attendance count would take.
        r#"{"format":"POA-STATION-DAILY-1","crew":null,"streak":3}"#,
        // Transposed keys.
        r#"{"crew":null,"format":"POA-STATION-DAILY-1"}"#,
        // The OUTPUT format tag on an input.
        r#"{"format":"POA-STATION-DAILY-OUT-1","crew":null}"#,
        // `false` is not a spelling of "absent".
        r#"{"format":"POA-STATION-DAILY-1","crew":false}"#,
        // Uppercase hex is a second spelling of one key.
        r#"{"format":"POA-STATION-DAILY-1","crew":"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"}"#,
        // Short digest.
        r#"{"format":"POA-STATION-DAILY-1","crew":"00"}"#,
        // Trailing byte after the object.
        r#"{"format":"POA-STATION-DAILY-1","crew":null} "#,
        // Whitespace inside: Lean's encoder emits none.
        r#"{"format": "POA-STATION-DAILY-1", "crew": null}"#,
        // Missing field.
        r#"{"format":"POA-STATION-DAILY-1"}"#,
        // Not an object.
        r#"[]"#,
    ] {
        assert_eq!(
            read(hostile),
            PoaStationDailyVerdict::Rejected,
            "an uncanonical request must be refused, not served: {hostile}"
        );
    }
}
