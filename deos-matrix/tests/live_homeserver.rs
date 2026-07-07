//! The **live homeserver** integration test — exercises the REAL `MatrixClient`
//! (matrix-rust-sdk) end to end against an actual running homeserver, NOT the
//! offline `MockSource`. It proves the hardened live path: build → login → sync →
//! list rooms → send (plain + membrane) → read back → extract the membrane as a
//! typed envelope.
//!
//! ## How to run it
//!
//! It is **creds-gated**: with no homeserver it is a no-op (so `cargo test` is
//! green in CI without network/creds). The turnkey path is the harness script —
//! it stands up a throwaway Conduit homeserver in Docker, registers two users,
//! runs every test here (incl. the cross-user A→B round-trip), and tears down:
//!
//! ```sh
//! ./scripts/live-test.sh          # full cycle (docker-compose.test.yml)
//! KEEP_HS=1 ./scripts/live-test.sh   # leave the homeserver up afterward
//! ```
//!
//! Or point it at a server by hand and it runs for real:
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

/// The two-user gating config for the cross-user A→B round-trip. Absent → no-op.
/// `DEOS_MATRIX_TEST_HS` plus a SECOND user's creds (the receiver). User A reuses
/// the `DEOS_MATRIX_TEST_USER/_PASS` triple above.
fn live_two_user_config() -> Option<(String, String, String, String, String)> {
    let hs = std::env::var("DEOS_MATRIX_TEST_HS").ok()?;
    let user_a = std::env::var("DEOS_MATRIX_TEST_USER").ok()?;
    let pass_a = std::env::var("DEOS_MATRIX_TEST_PASS").ok()?;
    let user_b = std::env::var("DEOS_MATRIX_TEST_USER_B").ok()?;
    let pass_b = std::env::var("DEOS_MATRIX_TEST_PASS_B").ok()?;
    Some((hs, user_a, pass_a, user_b, pass_b))
}

/// Sync a client until `pred` over its recent timeline for `room_id` is satisfied,
/// or `tries` syncs elapse (each followed by a short wait). The realistic
/// receive-side primitive: a real server takes a few syncs to deliver a freshly
/// sent event to the OTHER user. Returns the matching message or panics.
async fn sync_until(
    client: &MatrixClient,
    room_id: &str,
    tries: u32,
    label: &str,
    pred: impl Fn(&deos_matrix::TimelineMessage) -> bool,
) -> deos_matrix::TimelineMessage {
    for attempt in 0..tries {
        client.sync_once().await.expect("sync");
        let tl = client
            .recent_timeline(room_id, 100)
            .await
            .expect("timeline");
        if let Some(m) = tl.iter().find(|m| pred(m)) {
            return m.clone();
        }
        eprintln!(
            "  ({label}) not yet visible after sync {} — retrying",
            attempt + 1
        );
        tokio::time::sleep(std::time::Duration::from_millis(400)).await;
    }
    panic!("{label}: message never arrived on the receiver after {tries} syncs");
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

/// **The REAL executor-minted membrane fixture** — a `MembraneEnvelope` minted by
/// the genuine Lean-backed `World` executor in `starbridge-v2`
/// (`shared_fork::membrane_host::adapter_tests::bake_real_executor_membrane_fixture`,
/// run under `--features "embedded-executor dev-surfaces"`). It is the SAME
/// serializable wire shape `MockMembraneHost::sample_envelope()` produces, but its
/// `snapshot` field is a frustum of GENUINE `dregg_cell::Cell`s (the multiplayer
/// shared subrealm: a room focus + two user principals + three docs), committed
/// over the same `Cell`-postcard root the image folds — not a synthetic key→value
/// table. Loading it here lets the LIVE homeserver test ship an EXECUTOR-REAL
/// envelope A→B over a real Conduit server and prove those exact bytes survive
/// byte-intact + rehydrate on the receiving side. The executor-side
/// mint→rehydrate→drive→stitch (the half this workspace cannot link) is proven in
/// the same bake test that wrote this file. Together they demonstrate the full
/// cross-user loop across the honest workspace seam.
///
/// Returns `None` (and the test no-ops) if the fixture is absent — it is checked
/// in, but a clean checkout that has never run the bake test would lack it; the
/// live harness `scripts/live-test.sh` is what runs both halves.
fn real_executor_membrane() -> Option<deos_matrix::MembraneEnvelope> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/real_executor_membrane.json");
    let bytes = std::fs::read(&path).ok()?;
    let env: deos_matrix::MembraneEnvelope =
        serde_json::from_slice(&bytes).expect("the real executor membrane fixture is valid JSON");
    Some(env)
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
    let restored = MatrixClient::restore(&stored)
        .await
        .expect("restore session");
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
    let marker = format!(
        "deos-matrix live test {}",
        stored.session.tokens.access_token.len()
    );
    let sent_id = client
        .send_text(&room_id, &marker)
        .await
        .expect("send text");
    client.sync_once().await.expect("sync after send");
    let tl = client
        .recent_timeline(&room_id, 50)
        .await
        .expect("timeline");
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
    let tl = client
        .recent_timeline(&room_id, 50)
        .await
        .expect("timeline");
    let received = tl
        .iter()
        .find(|m| m.event_id == mem_id)
        .expect("membrane message read back");
    assert_eq!(received.kind, MessageKind::Membrane, "kind is Membrane");
    let back = received
        .membrane
        .as_ref()
        .expect("membrane envelope extracted from the wire");
    assert_eq!(
        back, &env,
        "the membrane round-tripped through the real server"
    );

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
    let tl = client
        .recent_timeline(&room_id, 50)
        .await
        .expect("timeline");
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
        received
            .object
            .as_ref()
            .expect("object extracted from the wire"),
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
    let aff_id = client
        .send_object(&room_id, "", &aff)
        .await
        .expect("send affordance");
    client.sync_once().await.expect("sync after affordance");
    let tl = client
        .recent_timeline(&room_id, 50)
        .await
        .expect("timeline");
    let r = tl
        .iter()
        .find(|m| m.event_id == aff_id)
        .expect("affordance read back");
    assert_eq!(r.kind, MessageKind::Object("affordance".into()));
    assert_eq!(r.object.as_ref().unwrap(), &aff);

    eprintln!(
        "LIVE OK: login+restore+sync+send(text)+send(membrane)+send(object×2)+extract all proven against {homeserver}"
    );
}

/// **THE CROSS-USER LIVE ROUND-TRIP** — two distinct deos-matrix clients (two
/// users) on a REAL homeserver: A creates a room and invites B, B accepts, then A
/// sends and B *receives over the wire* (real server delivery, separate sync
/// loops, separate SQLite stores). Proven legs:
///   1. a PLAIN text message A→B (regular chat round-trips);
///   2. a `MembraneEnvelope` (a forked-subrealm snapshot) A→B — B extracts the
///      typed envelope and it equals A's, byte-intact through the server;
///   3. a generalized `DreggObject` A→B — same extraction discipline.
///
/// This is the leg `live_login_sync_send_membrane_roundtrip` could NOT cover: that
/// one reads its OWN sent message back on a single client. Here the bytes leave one
/// process's client and arrive at a SECOND user's client through the homeserver —
/// the genuine "real messages over a real server round-trip" demonstration.
///
/// Creds-gated on the five-var two-user config; absent → no-op (CI stays green).
#[tokio::test]
async fn live_two_user_cross_user_roundtrip() {
    let Some((hs, user_a, pass_a, user_b, pass_b)) = live_two_user_config() else {
        eprintln!(
            "DEOS_MATRIX_TEST_USER_B/_PASS_B (+ the HS/USER/PASS triple) not set — \
             skipping the cross-user A→B live round-trip (see scripts/live-test.sh to run it)."
        );
        return;
    };

    // Two clients, two SQLite stores — genuinely separate users/devices.
    let (client_a, _stored_a) = MatrixClient::login_password(
        &hs,
        &tmp_store(),
        "live-A-passphrase",
        &user_a,
        &pass_a,
        "deos-matrix-live-A",
    )
    .await
    .expect("user A login");
    let (client_b, _stored_b) = MatrixClient::login_password(
        &hs,
        &tmp_store(),
        "live-B-passphrase",
        &user_b,
        &pass_b,
        "deos-matrix-live-B",
    )
    .await
    .expect("user B login");

    let uid_a = client_a.user_id().expect("A user id").to_string();
    let uid_b = client_b.user_id().expect("B user id").to_string();
    assert_ne!(uid_a, uid_b, "two genuinely distinct users");
    eprintln!("LIVE two-user: A={uid_a} B={uid_b} on {hs}");

    // A creates a room and invites B.
    let room_id = client_a
        .create_room(
            Some("deos-lab"),
            Some("the live deos-pilled room"),
            &[uid_b.as_str()],
        )
        .await
        .expect("A creates room + invites B");
    eprintln!("LIVE two-user: room {room_id} created by A, B invited");

    // B syncs, sees the invite, accepts it (real join over the wire).
    let mut joined = false;
    for attempt in 0..15 {
        client_b.sync_once().await.expect("B sync for invite");
        let invites = client_b.invited_rooms().await.expect("B invited rooms");
        if invites.iter().any(|r| r.room_id.as_str() == room_id) {
            client_b
                .accept_invite(&room_id)
                .await
                .expect("B accepts invite");
            joined = true;
            break;
        }
        // Maybe already auto-joined / already visible as joined.
        if client_b
            .joined_rooms()
            .await
            .expect("B joined")
            .iter()
            .any(|r| r.room_id.as_str() == room_id)
        {
            joined = true;
            break;
        }
        eprintln!(
            "  (invite) not visible to B yet after sync {} — retrying",
            attempt + 1
        );
        tokio::time::sleep(std::time::Duration::from_millis(400)).await;
    }
    assert!(joined, "B never saw/accepted the invite");
    client_b.sync_once().await.expect("B sync after join");
    eprintln!("LIVE two-user: B joined {room_id}");

    // ---- LEG 1: a PLAIN text message A→B ------------------------------------
    let marker = format!("hello from A · {}", uid_a);
    let text_id = client_a
        .send_text(&room_id, &marker)
        .await
        .expect("A sends text");
    let got = sync_until(&client_b, &room_id, 20, "text A→B", |m| {
        m.event_id == text_id || (m.body == marker && m.sender == uid_a)
    })
    .await;
    assert_eq!(got.body, marker, "B received A's exact text over the wire");
    assert_eq!(got.sender, uid_a, "sender is A");
    assert_eq!(got.kind, MessageKind::Text, "plain text kind");
    eprintln!("LIVE two-user: ✓ LEG 1 plain text A→B received by B");

    // ---- LEG 2: a MembraneEnvelope (dregg object) A→B -----------------------
    let env = MockMembraneHost::sample_envelope();
    let mem_id = client_a
        .send_membrane(&room_id, "", &env)
        .await
        .expect("A sends membrane");
    let got = sync_until(&client_b, &room_id, 20, "membrane A→B", |m| {
        m.event_id == mem_id
    })
    .await;
    assert_eq!(
        got.kind,
        MessageKind::Membrane,
        "B sees a Membrane-kind message"
    );
    let back = got
        .membrane
        .as_ref()
        .expect("B extracts the membrane envelope from the wire");
    assert_eq!(
        back, &env,
        "the MembraneEnvelope round-tripped A→B byte-intact through the real server"
    );
    // And it is rehydratable on B's side (the forward-compat + anti-substitution teeth hold).
    let host = deos_matrix::MockMembraneHost::seeded();
    assert!(
        back.is_rehydratable(),
        "B can rehydrate the received envelope"
    );
    deos_matrix::MembraneHost::rehydrate(&host, back).expect("B rehydrates the membrane");
    eprintln!("LIVE two-user: ✓ LEG 2 MembraneEnvelope A→B received + extracted + rehydrated by B");

    // ---- LEG 3: a generalized DreggObject A→B -------------------------------
    let obj = DreggObject::Cell(CellRef {
        cell_id: CellId::derive("!deoslab:deos.local"),
        label: "the deos-lab room cell".into(),
        cell_kind: Some("room".into()),
    });
    let obj_id = client_a
        .send_object(&room_id, "", &obj)
        .await
        .expect("A sends object");
    let got = sync_until(&client_b, &room_id, 20, "object A→B", |m| {
        m.event_id == obj_id
    })
    .await;
    assert_eq!(
        got.kind,
        MessageKind::Object("cell".into()),
        "B sees an Object(cell)"
    );
    assert_eq!(
        got.object.as_ref().expect("B extracts the object"),
        &obj,
        "DreggObject round-tripped A→B"
    );
    eprintln!("LIVE two-user: ✓ LEG 3 DreggObject A→B received + extracted by B");

    eprintln!(
        "LIVE OK (cross-user): A→B plain text + MembraneEnvelope + DreggObject all delivered \
         through the real homeserver {hs} and extracted typed on B."
    );
}

/// **THE EXECUTOR-REAL MEMBRANE A→B OVER A REAL HOMESERVER** — the wire half of the
/// full killer-primitive loop, with a GENUINE executor-minted membrane (not the
/// mock).
///
/// User A "screenshots a moment": loads the membrane the REAL Lean-backed `World`
/// executor minted in `starbridge-v2` (a frustum of genuine `dregg_cell::Cell`s — a
/// multiplayer shared subrealm), serialized to the fixture
/// `tests/fixtures/real_executor_membrane.json`. A ships it A→B over a real Conduit
/// homeserver (the SAME `send_membrane` wire path the mock uses — a custom field in
/// an `m.room.message`). B receives it through the server, extracts the typed
/// envelope, and proves:
///   * the EXACTLY-minted executor bytes survive the real server A→B byte-intact
///     (the received `MembraneEnvelope` equals the fixture the executor wrote);
///   * the anti-substitution `frustum_root` tooth + forward-compat version tooth
///     hold on the received envelope (B can rehydrate it).
///
/// The executor-side rehydrate→drive→stitch of THESE bytes (the conflict path, the
/// over-authorized lossy-drop, Σδ=0) is proven in the same `starbridge-v2` bake test
/// that wrote the fixture — the half this tokio/matrix-sdk workspace cannot link.
/// Together: mint(real executor) → carry(real Matrix server, HERE) →
/// rehydrate+drive+stitch(real executor). The seam is the fixture's wire bytes; both
/// halves RUN against their real substrate.
///
/// Creds-gated on the two-user config; the fixture must be present (the bake test
/// writes it). Absent either → no-op (CI stays green).
#[tokio::test]
async fn live_two_user_real_executor_membrane_roundtrip() {
    let Some((hs, user_a, pass_a, user_b, pass_b)) = live_two_user_config() else {
        eprintln!(
            "two-user creds not set — skipping the executor-real membrane A→B round-trip \
             (see scripts/live-test.sh)."
        );
        return;
    };
    let Some(real_env) = real_executor_membrane() else {
        eprintln!(
            "tests/fixtures/real_executor_membrane.json absent — skipping the executor-real \
             membrane A→B round-trip. Bake it first: in starbridge-v2, \
             `cargo test --no-default-features --features \"embedded-executor dev-surfaces\" \
              --lib bake_real_executor_membrane_fixture`."
        );
        return;
    };

    // Two clients, two SQLite stores — genuinely separate users/devices.
    let (client_a, _sa) = MatrixClient::login_password(
        &hs,
        &tmp_store(),
        "live-realA-pass",
        &user_a,
        &pass_a,
        "deos-matrix-realA",
    )
    .await
    .expect("user A login");
    let (client_b, _sb) = MatrixClient::login_password(
        &hs,
        &tmp_store(),
        "live-realB-pass",
        &user_b,
        &pass_b,
        "deos-matrix-realB",
    )
    .await
    .expect("user B login");
    let uid_b = client_b.user_id().expect("B user id").to_string();

    // A creates a room and invites B; B accepts (real join over the wire).
    let room_id = client_a
        .create_room(
            Some("deos-lab-real"),
            Some("executor-real membrane room"),
            &[uid_b.as_str()],
        )
        .await
        .expect("A creates room + invites B");
    let mut joined = false;
    for _ in 0..15 {
        client_b.sync_once().await.expect("B sync for invite");
        if client_b
            .invited_rooms()
            .await
            .expect("B invites")
            .iter()
            .any(|r| r.room_id.as_str() == room_id)
        {
            client_b
                .accept_invite(&room_id)
                .await
                .expect("B accepts invite");
            joined = true;
            break;
        }
        if client_b
            .joined_rooms()
            .await
            .expect("B joined")
            .iter()
            .any(|r| r.room_id.as_str() == room_id)
        {
            joined = true;
            break;
        }
        tokio::time::sleep(std::time::Duration::from_millis(400)).await;
    }
    assert!(joined, "B never saw/accepted the invite");
    client_b.sync_once().await.expect("B sync after join");

    // The fixture is genuinely executor-real (not the mock): its snapshot is the
    // multiplayer subrealm, so the cut carries >= 6 real cells.
    assert!(
        real_env.cut.cell_count >= 6,
        "the fixture is a real multiplayer subrealm (>=6 cells), got {}",
        real_env.cut.cell_count
    );
    assert!(
        real_env.is_rehydratable(),
        "the executor envelope is a supported wire version"
    );

    // A SCREENSHOTS THE MOMENT: ship the REAL executor membrane A→B over the server.
    let mem_id = client_a
        .send_membrane(&room_id, "", &real_env)
        .await
        .expect("A sends the executor-real membrane");

    // B RECEIVES IT THROUGH THE SERVER and extracts the typed envelope.
    let got = sync_until(&client_b, &room_id, 20, "executor membrane A→B", |m| {
        m.event_id == mem_id
    })
    .await;
    assert_eq!(
        got.kind,
        MessageKind::Membrane,
        "B sees a Membrane-kind message"
    );
    let back = got
        .membrane
        .as_ref()
        .expect("B extracts the executor membrane envelope from the wire");

    // BYTE-INTACT: the EXACTLY-minted executor bytes survived the real server A→B.
    assert_eq!(
        back, &real_env,
        "the executor-minted MembraneEnvelope round-tripped A→B byte-intact through the real server"
    );
    // The anti-substitution + forward-compat teeth hold on B's received copy.
    assert_eq!(
        back.frustum_root, real_env.frustum_root,
        "the frustum root survived A→B"
    );
    assert!(
        back.is_rehydratable(),
        "B can rehydrate the received executor envelope"
    );

    eprintln!(
        "LIVE OK (executor-real): A→B shipped the GENUINE executor-minted membrane \
         ({} cells, root {:02x}{:02x}{:02x}{:02x}) through {hs}; B extracted it byte-intact \
         + rehydratable. The executor-side rehydrate→drive→stitch (conflict + Σδ=0) is proven \
         in the starbridge-v2 bake test that wrote the fixture.",
        back.cut.cell_count,
        back.frustum_root[0],
        back.frustum_root[1],
        back.frustum_root[2],
        back.frustum_root[3],
    );
}

/// **THE CARD-FORK CARRY A→B OVER A REAL HOMESERVER** — Pillar 3 of distributed
/// deos: a co-driven card's portable fork-envelope crosses a LIVE Conduit between two
/// distinct users, byte-intact, so the two-cockpit stitch can land on both.
///
/// The card-fork envelope is sealed on the deos side as opaque `postcard` bytes plus
/// a claimed `fork_root` (the anti-substitution tooth's two inputs); this crate is
/// dependency-light and never links the card type, so the test carries a synthetic
/// sealed pair — the WIRE leg is identical regardless of who sealed the bytes. Proven:
///   1. A wraps the sealed pair into a card-carry `MembraneEnvelope`
///      ([`deos_matrix::card_fork_membrane`]) and ships it A→B over the real server
///      (the SAME `send_membrane` wire path the world-fork membrane uses);
///   2. B receives it through the server, extracts the typed envelope, routes it via
///      [`deos_matrix::as_card_fork_carry`], and recovers the sealed bytes + claimed
///      root EXACTLY (byte-intact) — the two inputs B's executor feeds the real
///      `open_envelope` tooth;
///   3. a FORGED carry (payload substituted, claimed root left unchanged) also crosses
///      byte-intact — so B's tooth sees bytes↔root disagree and REFUSES it (the wire
///      never heals the tampering, which would blind the tooth).
///
/// The executor-side open→rehydrate→stitch of these bytes (the tooth firing, both
/// edits surviving, an over-authorized fork contributing no patch) is proven where
/// the card type lives — `starbridge_v2::card_carry_bridge` (offline) and, in one
/// process over this same wire, its FULL_LOOP live test.
///
/// Creds-gated on the two-user config; absent → no-op (CI stays green).
#[tokio::test]
async fn live_two_user_card_fork_carry_roundtrip() {
    let Some((hs, user_a, pass_a, user_b, pass_b)) = live_two_user_config() else {
        eprintln!(
            "two-user creds not set — skipping the card-fork carry A→B round-trip \
             (see scripts/live-test.sh)."
        );
        return;
    };

    // Two clients, two SQLite stores — genuinely separate users/devices.
    let (client_a, _sa) = MatrixClient::login_password(
        &hs,
        &tmp_store(),
        "live-cardA-pass",
        &user_a,
        &pass_a,
        "deos-matrix-cardA",
    )
    .await
    .expect("user A login");
    let (client_b, _sb) = MatrixClient::login_password(
        &hs,
        &tmp_store(),
        "live-cardB-pass",
        &user_b,
        &pass_b,
        "deos-matrix-cardB",
    )
    .await
    .expect("user B login");
    let uid_b = client_b.user_id().expect("B user id").to_string();

    // A creates a room and invites B; B accepts (real join over the wire).
    let room_id = client_a
        .create_room(
            Some("deos-card-lab"),
            Some("co-driven card room"),
            &[uid_b.as_str()],
        )
        .await
        .expect("A creates room + invites B");
    let mut joined = false;
    for _ in 0..15 {
        client_b.sync_once().await.expect("B sync for invite");
        if client_b
            .invited_rooms()
            .await
            .expect("B invites")
            .iter()
            .any(|r| r.room_id.as_str() == room_id)
        {
            client_b
                .accept_invite(&room_id)
                .await
                .expect("B accepts invite");
            joined = true;
            break;
        }
        if client_b
            .joined_rooms()
            .await
            .expect("B joined")
            .iter()
            .any(|r| r.room_id.as_str() == room_id)
        {
            joined = true;
            break;
        }
        tokio::time::sleep(std::time::Duration::from_millis(400)).await;
    }
    assert!(joined, "B never saw/accepted the invite");
    client_b.sync_once().await.expect("B sync after join");

    // ---- The honest card-fork carry A→B -------------------------------------
    // A synthetic sealed pair (bytes + claimed fork_root). The wire leg is what the
    // real `distributed_card::seal_fork` output would traverse; byte-for-byte the same.
    let sealed_bytes = b"co-driven card-fork envelope :: postcard :: A's driven view".to_vec();
    let mut fork_root = [0u8; 32];
    for (i, r) in fork_root.iter_mut().enumerate() {
        *r = (i as u8).wrapping_mul(11).wrapping_add(5);
    }

    let carry_id = deos_matrix::send_card_fork(&client_a, &room_id, "", &sealed_bytes, fork_root)
        .await
        .expect("A ships the card-fork carry");
    let got = sync_until(&client_b, &room_id, 20, "card-fork carry A→B", |m| {
        m.event_id == carry_id
    })
    .await;
    assert_eq!(
        got.kind,
        MessageKind::Membrane,
        "B sees a Membrane-kind message (the card carry rides the membrane key)"
    );
    let back = got
        .membrane
        .as_ref()
        .expect("B extracts the card-carry envelope from the wire");
    let (got_bytes, got_root) = deos_matrix::as_card_fork_carry(back)
        .expect("B routes it to the card-fork path via the sturdyref scheme");
    assert_eq!(
        got_bytes, sealed_bytes,
        "the sealed card bytes crossed A→B byte-intact through the real server"
    );
    assert_eq!(
        got_root, fork_root,
        "the claimed fork_root crossed A→B byte-intact (the tooth's commitment input)"
    );
    eprintln!("LIVE two-user: ✓ card-fork carry A→B received + tooth inputs recovered byte-intact");

    // ---- A FORGED carry A→B: the wire preserves the tampering for refusal ----
    // Substitute the payload but keep the claimed root — this is exactly the input
    // that makes B's real `open_envelope` tooth fire (bytes↔root disagree). The point
    // here: the live server does NOT heal the substitution; both inputs arrive as sent,
    // so the tooth's refusal is decidable on B's side (never trust the wire).
    let mut forged_bytes = sealed_bytes.clone();
    forged_bytes.extend_from_slice(b"<<bob's sneaky injected node>>");
    let forged_id = deos_matrix::send_card_fork(&client_a, &room_id, "", &forged_bytes, fork_root) // SAME root
        .await
        .expect("A ships a forged carry (root left stale)");
    let got_forged = sync_until(&client_b, &room_id, 20, "forged carry A→B", |m| {
        m.event_id == forged_id
    })
    .await;
    let back_forged = got_forged
        .membrane
        .as_ref()
        .expect("B extracts the forged carry");
    let (fbytes, froot) =
        deos_matrix::as_card_fork_carry(back_forged).expect("still a card carry on the wire");
    assert_eq!(
        fbytes, forged_bytes,
        "the forged payload crossed as-is (the wire did not heal it)"
    );
    assert_eq!(
        froot, fork_root,
        "the claimed root is UNCHANGED — B's tooth sees bytes↔root disagree and REFUSES"
    );
    assert_ne!(
        fbytes, sealed_bytes,
        "the forged payload is distinguishable from the honest one"
    );
    eprintln!(
        "LIVE OK (card-fork carry): A→B shipped the sealed fork-envelope byte-intact through {hs}; \
         B recovered both tooth inputs, and a forged carry arrived with a stale root (refusable). \
         The executor-side open→rehydrate→stitch is proven in starbridge_v2::card_carry_bridge."
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
    assert!(
        client.user_id().is_some(),
        "discovery login resolved a session"
    );
    eprintln!(
        "LIVE OK: bare-server-name `.well-known` discovery login proven against {server_name}"
    );
}
