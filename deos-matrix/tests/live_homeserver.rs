//! The **live homeserver** integration test — exercises the REAL `MatrixClient`
//! (matrix-rust-sdk) end to end against an actual running homeserver, NOT the
//! offline `MockSource`. It proves the hardened live path: build → login → sync →
//! list rooms → send (plain + membrane) → read back → extract the membrane as a
//! typed envelope.
//!
//! ## How to run it
//!
//! It is **creds-gated**: with no homeserver it is a no-op (so `cargo test` is
//! green in CI without network/creds). Point it at a server and it runs for real:
//!
//! ```sh
//! # 1. a throwaway local conduit (single docker container, registration on):
//! docker run -d --name dm-conduit -p 6167:6167 \
//!   -e CONDUIT_CONFIG="" -e CONDUIT_SERVER_NAME=deos.local \
//!   -e CONDUIT_DATABASE_PATH=/var/lib/matrix-conduit/ \
//!   -e CONDUIT_DATABASE_BACKEND=rocksdb -e CONDUIT_PORT=6167 \
//!   -e CONDUIT_ADDRESS=0.0.0.0 -e CONDUIT_ALLOW_REGISTRATION=true \
//!   -e CONDUIT_ALLOW_FEDERATION=false matrixconduit/matrix-conduit:latest
//!
//! # 2. register a user (open registration):
//! curl -sX POST localhost:6167/_matrix/client/v3/register \
//!   -d '{"username":"ember","password":"hunter2hunter2",
//!        "auth":{"type":"m.login.dummy"}}'
//!
//! # 3. run the test:
//! DEOS_MATRIX_TEST_HS=http://localhost:6167 \
//! DEOS_MATRIX_TEST_USER=ember \
//! DEOS_MATRIX_TEST_PASS=hunter2hunter2 \
//!   cargo test --test live_homeserver -- --nocapture
//! ```
//!
//! This was the exact harness used to prove the live path during development
//! (conduit in docker, two registered users, a created room) — the end-to-end run
//! that a creds/network-less CI cannot reproduce, but any developer can.
//!
//! NATIVE-only: it drives a `#[tokio::main]`/multi-thread runtime against a real
//! socket and persists a SQLite store — neither exists on wasm32. The wasm
//! in-browser data-path proof is `source::wasm_tests` (run via `wasm-pack test`).
#![cfg(not(target_family = "wasm"))]

use std::path::PathBuf;

use deos_matrix::{
    Affordance, CellId, CellRef, DreggObject, MatrixClient, MessageKind, MockMembraneHost,
};

/// The gating env triple. Absent → the test is a no-op (CI-green without creds).
fn live_config() -> Option<(String, String, String)> {
    let hs = std::env::var("DEOS_MATRIX_TEST_HS").ok()?;
    let user = std::env::var("DEOS_MATRIX_TEST_USER").ok()?;
    let pass = std::env::var("DEOS_MATRIX_TEST_PASS").ok()?;
    Some((hs, user, pass))
}

fn tmp_store() -> PathBuf {
    let mut p = std::env::temp_dir();
    p.push(format!(
        "deos-matrix-livetest-{}",
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    p
}

#[tokio::test]
async fn live_login_sync_send_membrane_roundtrip() {
    let Some((homeserver, user, pass)) = live_config() else {
        eprintln!(
            "DEOS_MATRIX_TEST_HS/_USER/_PASS not set — skipping live homeserver test \
             (this is the creds-gated end-to-end; see the module docs to run it)."
        );
        return;
    };

    let store = tmp_store();
    let passphrase = "live-test-passphrase";

    // 1. LOGIN (the real password flow against the live server).
    let (client, stored) = MatrixClient::login_password(
        &homeserver,
        &store,
        passphrase,
        &user,
        &pass,
        "deos-matrix-livetest",
    )
    .await
    .expect("live login");
    assert!(client.user_id().is_some(), "logged in user id present");
    assert_eq!(stored.homeserver, homeserver);

    // 2. SESSION PERSISTENCE: restore from the stored session, no password.
    let restored = MatrixClient::restore(&stored).await.expect("restore session");
    assert_eq!(restored.user_id(), client.user_id());

    // 3. SYNC + ROOMS. The test user must be in at least one room; the harness
    //    (see module docs) creates one. If none, we cannot exercise send — fail
    //    loudly rather than silently pass.
    client.sync_once().await.expect("sync once");
    let rooms = client.joined_rooms().await.expect("joined rooms");
    assert!(
        !rooms.is_empty(),
        "the live test user is in no rooms — create one first (see module docs)"
    );
    let room_id = rooms[0].room_id.to_string();

    // 4. SEND a plain text message (real POST) and read it back.
    let marker = format!("deos-matrix live test {}", stored.session.tokens.access_token.len());
    let sent_id = client.send_text(&room_id, &marker).await.expect("send text");
    client.sync_once().await.expect("sync after send");
    let tl = client.recent_timeline(&room_id, 50).await.expect("timeline");
    assert!(
        tl.iter().any(|m| m.event_id == sent_id && m.body == marker),
        "our sent text message read back over the wire"
    );

    // 5. SEND a MEMBRANE-bearing message and read it back as a TYPED envelope —
    //    the deos-pilling over real Matrix (custom event key inside m.room.message).
    //    This test proves the WIRE leg: a `MembraneEnvelope` survives a real
    //    homeserver round-trip and re-extracts as a typed envelope. It uses the
    //    mock host's sample only because THIS standalone workspace cannot link the
    //    Lean-backed executor; the EXECUTOR-REAL round-trip (mint a genuine `Cell`
    //    frustum from `ForkMembraneHost` → serialize → rehydrate into a real `World`
    //    fork → drive a verified turn → stitch the real diff) is proven where the
    //    executor lives: `starbridge_v2::shared_fork` (`real_membrane_*` +
    //    `membrane_host::adapter_tests`). A `ForkMembraneHost` envelope is the SAME
    //    `MembraneEnvelope` shape this test ships, so the wire leg covers both.
    let env = MockMembraneHost::sample_envelope();
    let mem_id = client
        .send_membrane(&room_id, "", &env)
        .await
        .expect("send membrane");
    client.sync_once().await.expect("sync after membrane");
    let tl = client.recent_timeline(&room_id, 50).await.expect("timeline");
    let received = tl
        .iter()
        .find(|m| m.event_id == mem_id)
        .expect("membrane message read back");
    assert_eq!(received.kind, MessageKind::Membrane, "kind is Membrane");
    let back = received
        .membrane
        .as_ref()
        .expect("membrane envelope extracted from the wire");
    assert_eq!(back, &env, "the membrane round-tripped through the real server");

    // 6. SEND a generalized DREGG OBJECT (a non-membrane kind) and read it back as
    //    a typed object — the generalized envelope over real Matrix (the new
    //    `software.ember.deos.object` key with a `kind` tag).
    let obj = DreggObject::Cell(CellRef {
        cell_id: CellId::derive("!deoslab:deos.local"),
        label: "the deos-lab room cell".into(),
        cell_kind: Some("room".into()),
    });
    let obj_id = client
        .send_object(&room_id, "", &obj)
        .await
        .expect("send object");
    client.sync_once().await.expect("sync after object");
    let tl = client.recent_timeline(&room_id, 50).await.expect("timeline");
    let received = tl
        .iter()
        .find(|m| m.event_id == obj_id)
        .expect("object message read back");
    assert_eq!(
        received.kind,
        MessageKind::Object("cell".into()),
        "kind is Object(cell)"
    );
    assert_eq!(
        received.object.as_ref().expect("object extracted from the wire"),
        &obj,
        "the dregg object round-tripped through the real server"
    );

    // 7. A fireable AFFORDANCE object — the cap-gated-button kind — also round-trips.
    let aff = DreggObject::Affordance(Affordance {
        target_cell: CellId::derive("!deoslab:deos.local"),
        action: "approve".into(),
        label: "Approve the merge".into(),
        required_cap: "dregg://cap/approve".into(),
    });
    let aff_id = client.send_object(&room_id, "", &aff).await.expect("send affordance");
    client.sync_once().await.expect("sync after affordance");
    let tl = client.recent_timeline(&room_id, 50).await.expect("timeline");
    let r = tl.iter().find(|m| m.event_id == aff_id).expect("affordance read back");
    assert_eq!(r.kind, MessageKind::Object("affordance".into()));
    assert_eq!(r.object.as_ref().unwrap(), &aff);

    eprintln!(
        "LIVE OK: login+restore+sync+send(text)+send(membrane)+send(object×2)+extract all proven against {homeserver}"
    );
}

/// **Server-name `.well-known` discovery** — the bare-server-name login path a real
/// user types ("deos.local", not "https://…"). Creds-gated by a separate env triple
/// so it can target a server whose `.well-known` is set up (a full homeserver URL
/// still works via the main test). Absent → no-op.
#[tokio::test]
async fn live_servername_discovery_login() {
    let Ok(server_name) = std::env::var("DEOS_MATRIX_TEST_SERVERNAME") else {
        eprintln!(
            "DEOS_MATRIX_TEST_SERVERNAME not set — skipping bare-server-name discovery login test"
        );
        return;
    };
    let (Ok(user), Ok(pass)) = (
        std::env::var("DEOS_MATRIX_TEST_USER"),
        std::env::var("DEOS_MATRIX_TEST_PASS"),
    ) else {
        eprintln!("DEOS_MATRIX_TEST_USER/_PASS not set — skipping discovery login test");
        return;
    };

    let store = tmp_store();
    // Build from a BARE server name — exercises `.well-known`/versions discovery
    // (`server_name_or_homeserver_url`), the login-form "homeserver" field path.
    let (client, _stored) = MatrixClient::login_password(
        &server_name,
        &store,
        "discovery-test-passphrase",
        &user,
        &pass,
        "deos-matrix-discovery",
    )
    .await
    .expect("discovery login from a bare server name");
    assert!(client.user_id().is_some(), "discovery login resolved a session");
    eprintln!("LIVE OK: bare-server-name `.well-known` discovery login proven against {server_name}");
}
