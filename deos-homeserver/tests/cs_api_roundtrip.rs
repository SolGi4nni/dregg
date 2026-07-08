//! Proves the embedded continuwuity homeserver serves the client-server API a
//! Matrix client needs: versions handshake, open registration (m.login.dummy
//! UIAA), room create, message send, and read-back via /sync — the exact slice
//! `deos-matrix`'s matrix-rust-sdk client exercises for the membrane relay.
//!
//! Single test / single server per process: `run_with_args` installs a
//! process-global rustls provider (booting a second server in-process would
//! panic its thread), so the whole CS-API round-trip runs against one server.

use std::time::Duration;

use deos_homeserver::EmbeddedHomeserver;
use reqwest::blocking::Client;
use serde_json::{Value, json};

const SERVER_NAME: &str = "localhost";

#[test]
fn cs_api_roundtrip_against_embedded_homeserver() {
    let hs = EmbeddedHomeserver::start(SERVER_NAME).expect("boot embedded homeserver");
    // RocksDB open + services init takes a little while on first boot.
    let base = hs
        .wait_until_ready(Duration::from_secs(90))
        .expect("homeserver became ready")
        .to_string();

    let http = Client::builder()
        .timeout(Duration::from_secs(15))
        .build()
        .expect("http client");

    // 1) Versions handshake — the first thing any Matrix client asks.
    let versions: Value = http
        .get(format!("{base}/_matrix/client/versions"))
        .send()
        .expect("GET versions")
        .error_for_status()
        .expect("versions 200")
        .json()
        .expect("versions json");
    let vs = versions["versions"]
        .as_array()
        .expect("versions array present");
    assert!(!vs.is_empty(), "server advertised at least one CS version");

    // 2) Register a user via the open-registration UIAA flow.
    //    First POST (no auth) returns 401 + a session and the offered flows;
    //    with allow_registration + the yes_i_am_very... ack and no token/captcha,
    //    the only flow is [m.login.dummy]. Second POST completes it.
    let username = "alice";
    let password = "correct-horse-battery-staple";

    let first = http
        .post(format!("{base}/_matrix/client/v3/register"))
        .json(&json!({ "username": username, "password": password }))
        .send()
        .expect("register step 1");
    assert_eq!(
        first.status(),
        reqwest::StatusCode::UNAUTHORIZED,
        "registration begins with a UIAA challenge (401)"
    );
    let uiaa: Value = first.json().expect("uiaa json");
    let session = uiaa["session"].as_str().expect("uiaa session").to_string();
    let flows = uiaa["flows"].as_array().expect("uiaa flows");
    let offers_dummy = flows.iter().any(|f| {
        f["stages"]
            .as_array()
            .map(|s| s.iter().any(|st| st == "m.login.dummy"))
            .unwrap_or(false)
    });
    assert!(
        offers_dummy,
        "open registration offers the m.login.dummy flow"
    );

    let reg: Value = http
        .post(format!("{base}/_matrix/client/v3/register"))
        .json(&json!({
            "username": username,
            "password": password,
            "auth": { "type": "m.login.dummy", "session": session },
        }))
        .send()
        .expect("register step 2")
        .error_for_status()
        .expect("registration completes 200")
        .json()
        .expect("register json");

    let user_id = reg["user_id"].as_str().expect("user_id").to_string();
    let access_token = reg["access_token"]
        .as_str()
        .expect("access_token issued")
        .to_string();
    assert_eq!(user_id, format!("@{username}:{SERVER_NAME}"));

    let auth = |req: reqwest::blocking::RequestBuilder| req.bearer_auth(&access_token);

    // 3) Create a room.
    let room: Value = auth(
        http.post(format!("{base}/_matrix/client/v3/createRoom"))
            .json(&json!({ "name": "membrane", "preset": "private_chat" })),
    )
    .send()
    .expect("createRoom")
    .error_for_status()
    .expect("createRoom 200")
    .json()
    .expect("createRoom json");
    let room_id = room["room_id"].as_str().expect("room_id").to_string();

    // 4) Send an m.room.message (the MEMBRANE_EVENT_KEY shape the membrane uses).
    let body_text = "the membrane rides here";
    let txn = "deos-txn-1";
    let send: Value = auth(
        http.put(format!(
            "{base}/_matrix/client/v3/rooms/{room_id}/send/m.room.message/{txn}"
        ))
        .json(&json!({ "msgtype": "m.text", "body": body_text })),
    )
    .send()
    .expect("send message")
    .error_for_status()
    .expect("send 200")
    .json()
    .expect("send json");
    let event_id = send["event_id"].as_str().expect("event_id").to_string();
    assert!(event_id.starts_with('$'), "event id assigned: {event_id}");

    // 5) Read it back via /sync — proves the event round-trips through the
    //    server's timeline exactly as a client would receive it.
    let sync: Value = auth(http.get(format!("{base}/_matrix/client/v3/sync")))
        .send()
        .expect("sync")
        .error_for_status()
        .expect("sync 200")
        .json()
        .expect("sync json");

    let timeline = &sync["rooms"]["join"][&room_id]["timeline"]["events"];
    let events = timeline.as_array().expect("joined room timeline events");
    let found = events.iter().any(|e| {
        e["type"] == "m.room.message" && e["content"]["body"] == body_text && e["sender"] == user_id
    });
    assert!(
        found,
        "the sent m.room.message round-trips back through /sync; timeline was {timeline}"
    );

    // Explicit drop: the background boot thread is dropped and the temp DB tree
    // is best-effort removed (see EmbeddedHomeserver shutdown note).
    drop(hs);
}
