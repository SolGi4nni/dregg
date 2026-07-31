//! # sandstorm-serve — the SERVING weld, executable
//!
//! [`sandstorm-bridge`](sandstorm_bridge) models the whole signed-`.spk` grain
//! confinement + capability discipline and names two operated-layer welds as
//! follow-ups: the compute-tier `exec_workload` weld and the SERVING weld
//! (onto the hosting substrate's site-serving surface). This crate is the
//! serving weld, bound onto [`http-serve`](http_serve) — the substrate's
//! site-serving crate — for real:
//!
//! 1. [`custody`] — **archive-first grain custody**: install a REAL signed
//!    `.spk` (the Ed25519 signature over the archive is verified at install
//!    AND re-verified on every reopen; the App ID is the signing key), retain
//!    the exact bytes in an exclusively-locked, digest-chained archive with
//!    byte-exact replay, typed archive-ahead recovery, and hostile-tamper
//!    refusal.
//! 2. [`serve`] — **the serving core**: each request presents a real
//!    `dregg-auth` `dga1_` grain capability; its permission set is derived on
//!    the real rail per request ([`sandstorm_bridge::webauth_rail::derive_permissions`]
//!    re-verifies the ed25519 caveat chain — attenuation is live and only
//!    narrows), injected as the `X-Sandstorm-*` headers by the upstream
//!    [`HttpBridge`](sandstorm_bridge::bridge::HttpBridge), run against the
//!    grain's real `/var` cell heap, and a moved [`DataRoot`] is durably
//!    checkpointed archive-first BEFORE the response is acknowledged.
//! 3. [`surface`] — **the weld onto `http-serve`**: the handler + a stoppable
//!    daemon over `http-serve`'s hardened single-connection path (slow-loris /
//!    header / body bounds), with a pluggable [`TransportGate`] operator
//!    boundary (bind policy belongs to the operated deployment).
//! 4. [`body`] — **THE HONEST BODY SEAM**: the packaged app binary is NEVER
//!    executed here (that is the `exec_workload` weld — grain-jail / microVM —
//!    a separate lane). The surface takes a pluggable [`GrainBody`]; the
//!    default [`NoBody`] answers every request with a typed `503` naming the
//!    missing weld, and [`DemoNotesBody`] is an in-process `WebSession` body
//!    over the real cell heap, so the serving + auth + custody + checkpoint
//!    loop is real end-to-end without pretending to run the app.

pub mod body;
pub mod custody;
pub mod serve;
pub mod surface;

pub use body::{DemoNotesBody, GrainBody, GrainBodyKind, NoBody, NO_BODY_REFUSAL};
pub use custody::{
    GrainCustodyAnchorV1, GrainCustodyError, GrainCustodyRuntime, GrainCustodyStatusV1,
    GrainInstallation, GrainRecoveryReasonV1,
};
pub use serve::{GrainServeError, GrainServed, GrainServer, PresentedSession};
pub use surface::{grain_handler, GrainServeDaemon, OpenGate, TransportGate};

#[cfg(test)]
mod tests {
    use std::io::{Read, Write};
    use std::net::TcpStream;
    use std::sync::Arc;

    use ed25519_dalek::SigningKey;
    use grain_commons::{AgentBudget, AgentConfig, BrainChoice};
    use http_serve::Limits;
    use sandstorm_bridge::bridge::HttpRequest;
    use sandstorm_bridge::cell::Umem;
    use sandstorm_bridge::spk::base32;
    use sandstorm_bridge::webauth_rail::{attenuate_grain_cap, HostAuthority};

    use super::*;

    const GRAIN_ID: &str = "cell:demo-notes-1";
    const OWNER: &str = "u:alice";

    fn author_key(seed: u8) -> SigningKey {
        SigningKey::from_bytes(&[seed; 32])
    }

    /// A REAL signed `.spk` built through `grain_commons::publish`: genuine
    /// magic + xz + capnp wire, Ed25519 over the archive, facets view/edit.
    fn demo_spk(seed: u8) -> Vec<u8> {
        let config = AgentConfig::new(
            "Demo Notes Grain",
            ["view", "edit"],
            AgentBudget {
                max_spend: 300,
                max_tool_calls: 3,
            },
            BrainChoice::Replay,
        )
        .with_role("viewer", ["view"]);
        grain_commons::publish(&config, &author_key(seed)).expect("publishable demo grain")
    }

    /// The host powerbox authority every cap in this suite is minted from — and the ONE place
    /// this test process installs the Lean-verified PQ cores.
    ///
    /// A `dregg-auth` `dga1_` credential is HYBRID (ed25519 ∧ ML-DSA). `dregg-auth` installs a
    /// verified ML-DSA core only under its OWN `cfg(test)`, and so does
    /// `sandstorm_bridge::webauth_rail::HostAuthority::from_seed` — both inert here, where those
    /// crates are compiled as dependencies. With nothing installed `dregg-pq` refused the
    /// derivation with an uncatchable `process::abort()` (reported as SIGSEGV: this binary links
    /// SpiderMonkey, whose `mozalloc` redirects `abort()`), and the six tests that present a cap
    /// died having asserted nothing.
    ///
    /// ⚠ NOT `dregg_pq_testkit::install_at_process_start!()`: that macro needs `#[link_section]`,
    /// which this crate's `unsafe_code = "forbid"` rejects at compile time. `host()` is the
    /// crate's own choke point instead — it is the only `HostAuthority` construction outside the
    /// two attacker fixtures, and no cap can be minted, attenuated or presented without one.
    /// `install_or_panic` PANICS naming the missing directions if the linked archive is
    /// incomplete, rather than letting a test print `ok` about a cap nothing verified.
    fn host() -> HostAuthority {
        dregg_pq_testkit::install_or_panic();
        HostAuthority::from_seed([42u8; 32])
    }

    fn installed_custody(
        directory: &std::path::Path,
    ) -> (GrainCustodyRuntime, GrainCustodyAnchorV1) {
        let mut custody =
            GrainCustodyRuntime::open_or_create(directory, None).expect("fresh archive opens");
        let (_, anchor) = custody
            .install(GRAIN_ID, OWNER, &demo_spk(7))
            .expect("real signed spk installs");
        (custody, anchor)
    }

    fn editor_session(host: &HostAuthority) -> PresentedSession {
        let token = host
            .mint_grain_cap(GRAIN_ID, "u:alice", &["view", "edit"], None)
            .encode();
        PresentedSession {
            user_id: "u:alice".into(),
            username: "alice".into(),
            session_id: "s:1".into(),
            cap_token: token,
            presenter_subject: "u:alice".into(),
        }
    }

    fn viewer_attenuated_session(host: &HostAuthority) -> PresentedSession {
        // LIVE attenuation on the real rail: narrow the editor cap to view.
        let wide = host.mint_grain_cap(GRAIN_ID, "u:alice", &["view", "edit"], None);
        let narrowed = attenuate_grain_cap(wide, &["view"], None).encode();
        PresentedSession {
            user_id: "u:alice".into(),
            username: "alice".into(),
            session_id: "s:2".into(),
            cap_token: narrowed,
            presenter_subject: "u:alice".into(),
        }
    }

    fn open_server(custody: GrainCustodyRuntime, body: Box<dyn GrainBody>) -> GrainServer {
        GrainServer::open(custody, host().public(), body, true).expect("server opens")
    }

    // ── 1. Real .spk install + tamper refusal ────────────────────────────

    #[test]
    fn install_verifies_the_real_signature_and_refuses_tamper() {
        let directory = tempfile::tempdir().expect("tempdir");
        // macOS tempdirs live under the /var symlink; custody (correctly)
        // refuses symlinked components, so tests hand it the canonical path.
        let archive_root = directory
            .path()
            .canonicalize()
            .expect("canonical temp path");
        let spk = demo_spk(7);

        // A flipped byte deep in the container refuses BEFORE anything is retained.
        let mut tampered = spk.clone();
        let last = tampered.len() - 8;
        tampered[last] ^= 0xff;
        let mut custody =
            GrainCustodyRuntime::open_or_create(&archive_root, None).expect("fresh archive opens");
        assert!(matches!(
            custody.install(GRAIN_ID, OWNER, &tampered),
            Err(GrainCustodyError::Spk(_))
        ));
        assert!(matches!(custody.status(), GrainCustodyStatusV1::Empty));

        // The genuine package installs; the App ID is the signing key.
        let (installation, anchor) = custody
            .install(GRAIN_ID, OWNER, &spk)
            .expect("genuine spk installs");
        assert_eq!(
            installation.app_id,
            base32(author_key(7).verifying_key().as_bytes()),
            "App ID is the base32 of the Ed25519 signing key"
        );
        assert_eq!(installation.spec.declared_permissions, vec!["view", "edit"]);
        assert_eq!(installation.spk_bytes, spk, "exact bytes retained");
        assert_eq!(anchor.generation, 1);
        assert_eq!(anchor.data_root, Umem::new().commit().0, "genesis root");

        // A second install refuses.
        assert!(matches!(
            custody.install("cell:other", OWNER, &demo_spk(9)),
            Err(GrainCustodyError::AlreadyInstalled)
        ));
    }

    // ── 2. Byte-exact custody replay + typed recovery + tamper refusal ───

    #[test]
    fn reopen_replays_custody_byte_exactly() {
        let directory = tempfile::tempdir().expect("tempdir");
        // macOS tempdirs live under the /var symlink; custody (correctly)
        // refuses symlinked components, so tests hand it the canonical path.
        let archive_root = directory
            .path()
            .canonicalize()
            .expect("canonical temp path");
        let spk = demo_spk(7);
        let (mut custody, _anchor) = installed_custody(&archive_root);
        let mut var = custody.head_var();
        var.put("notes/hello", b"hello dregg".to_vec());
        let anchor = custody.checkpoint(&var).expect("checkpoint appends");
        drop(custody);

        let reopened = GrainCustodyRuntime::open_or_create(&archive_root, Some(&anchor))
            .expect("anchored reopen replays");
        assert!(matches!(
            reopened.status(),
            GrainCustodyStatusV1::Ready { .. }
        ));
        let installation = reopened.installation().expect("installed");
        assert_eq!(installation.spk_bytes, spk, "exact .spk bytes replayed");
        assert_eq!(installation.grain_cell_id, GRAIN_ID);
        let var = reopened.head_var();
        assert_eq!(var.get("notes/hello"), Some(&b"hello dregg"[..]));
        assert_eq!(
            var.commit().0,
            anchor.data_root,
            "the /var recommits to the anchored root"
        );
    }

    #[test]
    fn archive_ahead_reopen_requires_typed_acknowledgement() {
        let directory = tempfile::tempdir().expect("tempdir");
        // macOS tempdirs live under the /var symlink; custody (correctly)
        // refuses symlinked components, so tests hand it the canonical path.
        let archive_root = directory
            .path()
            .canonicalize()
            .expect("canonical temp path");
        let (custody, install_anchor) = installed_custody(&archive_root);
        drop(custody);

        // The operator lost the anchor persistence race: archive is one ahead.
        let mut reopened = GrainCustodyRuntime::open_or_create(&archive_root, None)
            .expect("archive-ahead reopen is typed, not refused");
        let GrainCustodyStatusV1::RecoveryRequired {
            acknowledged_base,
            candidate,
            reason,
        } = reopened.status()
        else {
            panic!("archive-ahead restart must require recovery");
        };
        assert_eq!(acknowledged_base, None);
        assert_eq!(candidate, install_anchor);
        assert_eq!(
            reason,
            GrainRecoveryReasonV1::RestartedArchiveAheadWithoutAnchor
        );

        // Mutations refuse until the exact candidate is acknowledged.
        assert!(matches!(
            reopened.checkpoint(&Umem::new()),
            Err(GrainCustodyError::RecoveryRequired)
        ));
        let mut substituted = candidate.clone();
        substituted.generation += 1;
        assert!(matches!(
            reopened.acknowledge_archive_head(&substituted),
            Err(GrainCustodyError::AcknowledgementSubstitution)
        ));
        reopened
            .acknowledge_archive_head(&candidate)
            .expect("exact acknowledgement settles");
        assert!(matches!(
            reopened.status(),
            GrainCustodyStatusV1::Ready { .. }
        ));
    }

    #[test]
    fn tampered_or_diverged_archives_refuse_open() {
        let directory = tempfile::tempdir().expect("tempdir");
        // macOS tempdirs live under the /var symlink; custody (correctly)
        // refuses symlinked components, so tests hand it the canonical path.
        let archive_root = directory
            .path()
            .canonicalize()
            .expect("canonical temp path");
        let (mut custody, install_anchor) = installed_custody(&archive_root);
        let mut var = custody.head_var();
        var.put("k", b"v".to_vec());
        let head = custody.checkpoint(&var).expect("checkpoint");
        drop(custody);

        // An anchor older than the archive base diverges (more than one ahead).
        let mut third = var.clone();
        third.put("k2", b"v2".to_vec());
        {
            let mut runtime =
                GrainCustodyRuntime::open_or_create(&archive_root, Some(&head)).expect("open");
            runtime.checkpoint(&third).expect("third record");
        }
        assert!(matches!(
            GrainCustodyRuntime::open_or_create(&archive_root, Some(&install_anchor)),
            Err(GrainCustodyError::AnchorArchiveDiverged)
        ));

        // A flipped byte in a record refuses the whole open.
        let record_path = archive_root.join(format!("{:020}.grain", 2));
        let mut bytes = std::fs::read(&record_path).expect("read record");
        let last = bytes.len() - 1;
        bytes[last] ^= 1;
        std::fs::write(&record_path, bytes).expect("tamper record");
        assert!(GrainCustodyRuntime::open_or_create(&archive_root, Some(&head)).is_err());
    }

    // ── 3/4/5. Cap-derived identity headers, live attenuation, refusals ──

    #[test]
    fn a_valid_cap_yields_the_derived_identity_and_permissions() {
        let directory = tempfile::tempdir().expect("tempdir");
        // macOS tempdirs live under the /var symlink; custody (correctly)
        // refuses symlinked components, so tests hand it the canonical path.
        let archive_root = directory
            .path()
            .canonicalize()
            .expect("canonical temp path");
        let (custody, _) = installed_custody(&archive_root);
        let mut server = open_server(custody, Box::new(DemoNotesBody));

        let served = server
            .serve(&editor_session(&host()), &HttpRequest::get("/whoami"), 1000)
            .expect("serve");
        assert_eq!(served.response.status, 200);
        let echo: serde_json::Value =
            serde_json::from_slice(&served.response.body).expect("whoami json");
        assert_eq!(echo["user_id"], "u:alice");
        assert_eq!(echo["username"], "alice");
        assert_eq!(echo["session_id"], "s:1");
        // The permission set is DERIVED from the cap on the real rail.
        assert_eq!(
            echo["permissions"],
            serde_json::json!(["edit", "view"]),
            "X-Sandstorm-Permissions is the cap's facet set"
        );
    }

    #[test]
    fn an_attenuated_cap_yields_reduced_permissions_live() {
        let directory = tempfile::tempdir().expect("tempdir");
        // macOS tempdirs live under the /var symlink; custody (correctly)
        // refuses symlinked components, so tests hand it the canonical path.
        let archive_root = directory
            .path()
            .canonicalize()
            .expect("canonical temp path");
        let (custody, install_anchor) = installed_custody(&archive_root);
        let mut server = open_server(custody, Box::new(DemoNotesBody));
        let session = viewer_attenuated_session(&host());

        let who = server
            .serve(&session, &HttpRequest::get("/whoami"), 1000)
            .expect("serve");
        let echo: serde_json::Value =
            serde_json::from_slice(&who.response.body).expect("whoami json");
        assert_eq!(
            echo["permissions"],
            serde_json::json!(["view"]),
            "attenuation narrowed the derived header set"
        );

        // The narrowed cap cannot write: the app reads the header and 403s,
        // and nothing moves the committed root.
        let write = server
            .serve(&session, &HttpRequest::post("/pwn", b"nope".to_vec()), 1000)
            .expect("serve");
        assert_eq!(write.response.status, 403);
        assert!(!write.checkpointed);
        assert_eq!(write.anchor, install_anchor);
    }

    #[test]
    fn missing_forged_or_leaked_caps_are_refused_inertly() {
        let directory = tempfile::tempdir().expect("tempdir");
        // macOS tempdirs live under the /var symlink; custody (correctly)
        // refuses symlinked components, so tests hand it the canonical path.
        let archive_root = directory
            .path()
            .canonicalize()
            .expect("canonical temp path");
        let (custody, install_anchor) = installed_custody(&archive_root);
        let mut server = open_server(custody, Box::new(DemoNotesBody));

        // A forged cap minted under a different root.
        let attacker = HostAuthority::from_seed([66u8; 32]);
        let forged = PresentedSession {
            cap_token: attacker
                .mint_grain_cap(GRAIN_ID, "u:mallory", &["view", "edit"], None)
                .encode(),
            user_id: "u:mallory".into(),
            username: "mallory".into(),
            session_id: "s:f".into(),
            presenter_subject: "u:mallory".into(),
        };
        // A genuine cap over a DIFFERENT grain.
        let cross = PresentedSession {
            cap_token: host()
                .mint_grain_cap("cell:other", "u:mallory", &["view", "edit"], None)
                .encode(),
            ..forged.clone()
        };
        // A leaked cap sealed to alice, presented by mallory.
        let leaked = PresentedSession {
            cap_token: host()
                .mint_grain_cap(GRAIN_ID, "u:alice", &["view", "edit"], None)
                .encode(),
            ..forged.clone()
        };
        // Garbage instead of a token.
        let garbage = PresentedSession {
            cap_token: "not-a-dga1-token".into(),
            ..forged.clone()
        };
        for hostile in [forged, cross, leaked, garbage] {
            let served = server
                .serve(
                    &hostile,
                    &HttpRequest::post("/pwn", b"owned".to_vec()),
                    1000,
                )
                .expect("serve refuses inertly");
            assert_eq!(served.response.status, 403);
            assert!(!served.checkpointed, "no state moved");
            assert_eq!(served.anchor, install_anchor);
        }
    }

    // ── 6. The honest body seam ──────────────────────────────────────────

    #[test]
    fn no_body_refuses_with_a_typed_503_naming_the_missing_weld() {
        let directory = tempfile::tempdir().expect("tempdir");
        // macOS tempdirs live under the /var symlink; custody (correctly)
        // refuses symlinked components, so tests hand it the canonical path.
        let archive_root = directory
            .path()
            .canonicalize()
            .expect("canonical temp path");
        let (custody, install_anchor) = installed_custody(&archive_root);
        let mut server = open_server(custody, Box::new(NoBody));
        assert_eq!(server.body_kind(), GrainBodyKind::NoBody);

        // Even a fully-privileged cap gets the typed refusal.
        let served = server
            .serve(
                &editor_session(&host()),
                &HttpRequest::get("/anything"),
                1000,
            )
            .expect("serve");
        assert_eq!(served.response.status, 503);
        assert_eq!(served.response.body, NO_BODY_REFUSAL.as_bytes());
        let refusal: serde_json::Value =
            serde_json::from_slice(&served.response.body).expect("typed json");
        assert_eq!(refusal["refusal"], "grain-serve.exec-weld-unavailable");
        assert_eq!(refusal["app_executed"], false);
        assert!(!served.checkpointed);
        assert_eq!(served.anchor, install_anchor);

        // A forged cap still refuses 403 BEFORE the body seam is reached.
        let attacker = HostAuthority::from_seed([66u8; 32]);
        let forged = PresentedSession {
            cap_token: attacker
                .mint_grain_cap(GRAIN_ID, "u:mallory", &["view"], None)
                .encode(),
            user_id: "u:mallory".into(),
            username: "mallory".into(),
            session_id: "s:f".into(),
            presenter_subject: "u:mallory".into(),
        };
        let refused = server
            .serve(&forged, &HttpRequest::get("/anything"), 1000)
            .expect("serve");
        assert_eq!(refused.response.status, 403);
    }

    // ── 7. Demo round trip: mutation moves the root and survives reopen ──

    #[test]
    fn demo_round_trip_checkpoints_and_survives_reopen() {
        let directory = tempfile::tempdir().expect("tempdir");
        // macOS tempdirs live under the /var symlink; custody (correctly)
        // refuses symlinked components, so tests hand it the canonical path.
        let archive_root = directory
            .path()
            .canonicalize()
            .expect("canonical temp path");
        let (custody, install_anchor) = installed_custody(&archive_root);
        let mut server = open_server(custody, Box::new(DemoNotesBody));
        let session = editor_session(&host());

        let write = server
            .serve(
                &session,
                &HttpRequest::post("/pad/welcome", b"hello dregg".to_vec()),
                1000,
            )
            .expect("serve");
        assert_eq!(write.response.status, 200);
        assert!(write.checkpointed, "the mutation was durably checkpointed");
        assert_ne!(
            write.anchor.data_root, install_anchor.data_root,
            "the DataRoot checkpoint moved"
        );
        assert_eq!(write.anchor.generation, install_anchor.generation + 1);
        let anchor = write.anchor.clone();
        drop(server);

        // Reopen custody at the persisted anchor; the state survived.
        let custody = GrainCustodyRuntime::open_or_create(&archive_root, Some(&anchor))
            .expect("anchored reopen");
        let mut server = open_server(custody, Box::new(DemoNotesBody));
        assert_eq!(server.data_root().0, anchor.data_root);
        let read = server
            .serve(&session, &HttpRequest::get("/pad/welcome"), 2000)
            .expect("serve");
        assert_eq!(read.response.status, 200);
        assert_eq!(read.response.body, b"hello dregg");
        assert!(!read.checkpointed, "a pure read moves nothing");
        assert_eq!(read.data_root.0, anchor.data_root);
    }

    // ── 8. The weld onto http-serve, over a real socket ──────────────────

    fn raw_http(addr: std::net::SocketAddr, request: &str) -> (u16, Vec<u8>) {
        let mut stream = TcpStream::connect(addr).expect("connect");
        stream.write_all(request.as_bytes()).expect("write request");
        let mut response = Vec::new();
        stream.read_to_end(&mut response).expect("read response");
        let head_end = response
            .windows(4)
            .position(|w| w == b"\r\n\r\n")
            .expect("response head");
        let head = std::str::from_utf8(&response[..head_end]).expect("utf-8 head");
        let status: u16 = head
            .split(' ')
            .nth(1)
            .expect("status code")
            .parse()
            .expect("numeric status");
        (status, response[head_end + 4..].to_vec())
    }

    #[test]
    fn the_daemon_serves_the_grain_over_http_serve() {
        let directory = tempfile::tempdir().expect("tempdir");
        // macOS tempdirs live under the /var symlink; custody (correctly)
        // refuses symlinked components, so tests hand it the canonical path.
        let archive_root = directory
            .path()
            .canonicalize()
            .expect("canonical temp path");
        let (custody, _) = installed_custody(&archive_root);
        let server = open_server(custody, Box::new(DemoNotesBody));
        let daemon = GrainServeDaemon::spawn(
            "127.0.0.1:0".parse().expect("addr"),
            Arc::new(OpenGate),
            server,
            Limits::default(),
        )
        .expect("loopback daemon spawns");
        let addr = daemon.local_addr();
        let token = host()
            .mint_grain_cap(GRAIN_ID, "u:alice", &["view", "edit"], None)
            .encode();

        // A capless request is refused with a typed 401.
        let (status, body) = raw_http(addr, "GET /pad/x HTTP/1.1\r\nHost: g\r\n\r\n");
        assert_eq!(status, 401);
        let refusal: serde_json::Value = serde_json::from_slice(&body).expect("typed refusal");
        assert_eq!(refusal["refusal"], "grain-serve.capability-required");

        // A smuggled duplicate cap header is refused fail-closed (http-serve's
        // duplicate-safe header read yields None).
        let (status, _) = raw_http(
            addr,
            &format!(
                "GET /pad/x HTTP/1.1\r\nHost: g\r\nx-dregg-grain-cap: {token}\r\nx-dregg-grain-cap: {token}\r\nx-dregg-presenter: u:alice\r\n\r\n"
            ),
        );
        assert_eq!(status, 401);

        // Write then read through the daemon with the real cap.
        let (status, body) = raw_http(
            addr,
            &format!(
                "POST /pad/welcome HTTP/1.1\r\nHost: g\r\nx-dregg-grain-cap: {token}\r\nx-dregg-presenter: u:alice\r\nContent-Length: 11\r\n\r\nhello dregg"
            ),
        );
        assert_eq!(status, 200);
        assert_eq!(body, b"stored");
        let (status, body) = raw_http(
            addr,
            &format!(
                "GET /pad/welcome HTTP/1.1\r\nHost: g\r\nx-dregg-grain-cap: {token}\r\nx-dregg-presenter: u:alice\r\n\r\n"
            ),
        );
        assert_eq!(status, 200);
        assert_eq!(body, b"hello dregg");

        // The status surface reports the honest body kind and live root.
        let (status, body) = raw_http(addr, "GET /__grain/status HTTP/1.1\r\nHost: g\r\n\r\n");
        assert_eq!(status, 200);
        let status_json: serde_json::Value = serde_json::from_slice(&body).expect("status json");
        assert_eq!(status_json["grain_cell_id"], GRAIN_ID);
        assert_eq!(status_json["body"], "in-process-demo");
        assert_eq!(status_json["custody_generation"], 2);

        // Shutdown sleeps the grain and returns the final anchor; the served
        // note survives a fresh reopen at that anchor.
        let final_anchor = daemon.shutdown().expect("clean shutdown");
        let custody = GrainCustodyRuntime::open_or_create(&archive_root, Some(&final_anchor))
            .expect("reopen at the shutdown anchor");
        assert_eq!(
            custody.head_var().get("notes/pad/welcome"),
            Some(&b"hello dregg"[..])
        );
    }
}
