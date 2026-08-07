//! THE OPERATOR DRILL: run the Path of Angels first-turn ceremony with the actual
//! `dregg-node` and `poa-curator` BINARIES, as real OS processes, against a real
//! redb store and a real TCP-bound HTTP server — and watch `latest_height` move.
//!
//! # What this is for
//!
//! `poa_signal_first_turn_e2e` proves the MILESTONE: a judged Signal turn settles.
//! It proves it entirely in-process, so it cannot answer the operator's question,
//! which is different: *are the commands sufficient to do this on a node I did not
//! write?* A ceremony whose steps exist only as Rust functions is a ceremony nobody
//! can perform. This drill answers that question by refusing to call any of them
//! directly: steps 1 through 6 are `std::process::Command`, and the only thing this
//! harness does in-process is the part that has no command (see the deviation
//! below).
//!
//! ```text
//! 1. dregg-node poa-slot-opening-preview      SUBPROCESS  (node stopped)
//! 2. poa-curator  sign-slot-opening           SUBPROCESS  (CURATOR KEY)
//! 3. dregg-node init-poa-signal-slot          SUBPROCESS  (node stopped)
//! 4. dregg-node poa-signal-instance-preview   SUBPROCESS  (node stopped)  ← new
//! 5. dregg-node poa-signal-submit-claim       SUBPROCESS  (node running) ← new
//! 6.   …its --await-latest-height polls GET /status over real TCP           ← new
//! ```
//!
//! The node is genuinely STOPPED for steps 1-4 and genuinely RUNNING for 5-6: redb
//! is single-writer, so the harness must drop its store before the subprocesses can
//! open it, and re-open it afterwards. That ordering is not a convenience here, it
//! is the operational constraint of the real ceremony, exercised.
//!
//! # ⚑ THE ONE DEVIATION, STATED PLAINLY
//!
//! The PoA Signal HEAD and the curator PIN are installed in-process, not through
//! `dregg-node init-poa-signal` / `init-poa-galley-world`. That is not a shortcut
//! taken for speed — those two commands cannot run against a locally minted
//! federation at all:
//!
//! * `Poag1Bundle::bind_deployment_scope` refuses with
//!   `mission 1 federation 70b7fa4c… != deployed federation …` — the shipped POAG1
//!   catalog (`poa/artifacts/poag1/catalog.json`) NAMES the live federation id, so
//!   the content bundle is bound to that one deployment and cannot authenticate a
//!   different one;
//! * re-emitting content for a local federation is Lean `Emit` work, out of scope
//!   here;
//! * and `scripts/poa-devnet-manifest.mjs` additionally refuses any PoA genesis
//!   whose `initial_cells` is not exactly the two zero-balance wells.
//!
//! So the head/pin installation is stubbed and everything downstream of it — which
//! is the entire set of steps that had no command — is real. On the LIVE node the
//! head and pin are already installed, so the drill covers exactly the remaining
//! work.
//!
//! # ⚠ Requires a freshly built binary, so it does not run by default
//!
//! `#[ignore]`, because a lib unit test has no `CARGO_BIN_EXE_*` and a drill that
//! silently graded a stale binary would be worse than one that does not run. Build,
//! then drive it:
//!
//! ```text
//! cargo build -p dregg-node --bin dregg-node && cargo build -p poa-curator
//! cargo test -p dregg-node --lib -- --ignored --nocapture \
//!   poa_signal_slot_first_turn_rehearsal
//! ```

#![cfg(test)]

use std::net::SocketAddr;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use dregg_types::hex_encode;
use zeroize::Zeroizing;

use crate::blocklace_sync::run_blocklace_sync_with_policy;
use crate::state::NodeState;

const SLOT: u64 = 9;
const MISSION_ID: u64 = 1;
/// The curator's slot secret for this drill. A real deployment draws it off-line
/// (`openssl rand -hex 32`) and the node never mints one.
const SECRET_HEX: &str = "7777777777777777777777777777777777777777777777777777777777777777";
/// The player's Ed25519 seed.
const PLAYER_SEED_HEX: &str = "c7c7c7c7c7c7c7c7c7c7c7c7c7c7c7c7c7c7c7c7c7c7c7c7c7c7c7c7c7c7c7c7";

/// The workspace `target/<profile>/` a `cargo test` of this crate builds into.
fn binary(name: &str) -> PathBuf {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("node/ has a workspace parent");
    for profile in ["debug", "release"] {
        let candidate = workspace.join("target").join(profile).join(name);
        if candidate.is_file() {
            return candidate;
        }
    }
    panic!(
        "{name} is not built. This drill runs the REAL binaries; build them first:\n  \
         cargo build -p dregg-node --bin dregg-node && cargo build -p poa-curator"
    );
}

/// Run one ceremony step as a real process. Prints the exact command, because the
/// point of the drill is the COMMAND LIST an operator will run on the live node.
fn step(label: &str, program: &Path, args: &[&str]) -> String {
    eprintln!(
        "\n$ {} {}\n    # step: {label}",
        program.display(),
        args.join(" ")
    );
    let output = Command::new(program)
        .args(args)
        .output()
        .unwrap_or_else(|error| panic!("{label}: cannot spawn {}: {error}", program.display()));
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    // The node logs its verified-core installations to stderr on every invocation;
    // print only what is not that noise.
    for line in stderr.lines().filter(|line| !line.contains(" INFO ")) {
        eprintln!("  ! {line}");
    }
    for line in stdout.lines() {
        eprintln!("  > {line}");
    }
    assert!(
        output.status.success(),
        "{label} FAILED ({}). This is a ceremony step with no fallback; a drill that \
         continued past it would be reporting a settle nobody could reproduce.\nstdout: \
         {stdout}\nstderr: {stderr}",
        output.status
    );
    stdout
}

/// THE DRILL.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
#[ignore = "runs the built dregg-node / poa-curator binaries; build them first (see module docs)"]
async fn the_first_turn_ceremony_settles_when_driven_by_the_commands() {
    let _ = rustls::crypto::ring::default_provider().install_default();
    let _ = crate::install_mldsa_verified_keygen_core_real();
    let _ = crate::install_mldsa_verified_sign_core_real();
    let _ = crate::install_mldsa_verified_verify_core();
    assert!(
        dregg_lean_ffi::poa_ffi::poa_signal_judge_available()
            && dregg_lean_ffi::poa_slot_derive_ffi::poa_slot_derive_available(),
        "this drill requires the linked native judge and slot-derivation exports"
    );

    let node_bin = binary("dregg-node");
    let curator_bin = binary("poa-curator");
    let work = tempfile::tempdir().expect("tempdir");
    let data_dir = work.path().join("node-0");
    std::fs::create_dir_all(&data_dir).expect("data dir");
    let secret_file = work.path().join("slot.secret");
    std::fs::write(&secret_file, SECRET_HEX).expect("slot secret");
    let player_key_file = work.path().join("player.key");
    std::fs::write(&player_key_file, PLAYER_SEED_HEX).expect("player key");
    let curator_secret = work.path().join("curator.secret");
    let curator_pin = work.path().join("curator-pin.json");

    let player =
        dregg_sdk::AgentCipherclerk::from_key_bytes(Zeroizing::new(parse32(PLAYER_SEED_HEX)));
    let player_key_hex = hex_encode(&player.public_key().0);

    // ── STEP 0 — the curator draws its key. Off the node, as it must be. ─────
    step(
        "poa-curator keygen",
        &curator_bin,
        &[
            "keygen",
            "--secret",
            curator_secret.to_str().unwrap(),
            "--pin",
            curator_pin.to_str().unwrap(),
        ],
    );
    let pin: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&curator_pin).expect("pin document"))
            .expect("pin JSON");
    let curator_public_key = parse32(
        pin["curator_pubkey"]
            .as_str()
            .expect("the pin names a curator public key"),
    );

    // ── PHASE 0 (the deviation): head + curator pin, in-process. ─────────────
    // Everything after this line is a real process. See the module docblock for
    // why these two cannot be.
    let authority_hex = {
        let state = NodeState::new(&data_dir, vec![]).expect("build NodeState");
        let federation_id;
        {
            let mut s = state.write().await;
            s.unlocked = true;
            let node_pk = s.cclerk.public_key();
            let node_seed = s.cclerk.gossip_signing_key().to_bytes();
            let (node_ml_dsa, _) = dregg_federation::frost::MlDsaSigningKey::from_seed(&node_seed);
            s.set_federation_keys_hybrid(vec![node_pk], vec![node_ml_dsa]);
            federation_id = crate::executor_setup::federation_id_for_executor(&s);
            let head =
                crate::poa_signal_adapter::fixture_signal_head_for_finality_test(federation_id);
            s.store
                .initialize_poa_signal_head(&head)
                .expect("initialize the PoA Signal authority head");
            s.store
                .install_poa_world_curator_pin_v1(curator_public_key)
                .expect("pin the curator key");
        }
        // STOP THE NODE. redb is single-writer: until this store is dropped, no
        // subprocess can open the data directory at all.
        drop(state);
        hex_encode(&federation_id)
    };

    let preview_path = work.path().join("slot-opening-preview.json");
    let envelope_path = work.path().join("slot-opening.json");
    let instance_path = work.path().join("instance.json");
    let slot_text = SLOT.to_string();
    let mission_text = MISSION_ID.to_string();

    // ── STEP 1 ────────────────────────────────────────────────────────────────
    step(
        "poa-slot-opening-preview",
        &node_bin,
        &[
            "poa-slot-opening-preview",
            "--data-dir",
            data_dir.to_str().unwrap(),
            "--authority-id",
            &authority_hex,
            "--mission-id",
            &mission_text,
            "--slot",
            &slot_text,
            "--secret-file",
            secret_file.to_str().unwrap(),
            "--output",
            preview_path.to_str().unwrap(),
        ],
    );

    // ── STEP 2 — THE CURATOR KEY, and the only step that touches it ───────────
    step(
        "poa-curator sign-slot-opening",
        &curator_bin,
        &[
            "sign-slot-opening",
            "--secret",
            curator_secret.to_str().unwrap(),
            "--pin",
            curator_pin.to_str().unwrap(),
            "--preview",
            preview_path.to_str().unwrap(),
            "--output",
            envelope_path.to_str().unwrap(),
        ],
    );

    // ── STEP 3 ────────────────────────────────────────────────────────────────
    let installed = step(
        "init-poa-signal-slot",
        &node_bin,
        &[
            "init-poa-signal-slot",
            "--data-dir",
            data_dir.to_str().unwrap(),
            "--authority-id",
            &authority_hex,
            "--mission-id",
            &mission_text,
            "--slot",
            &slot_text,
            "--secret-file",
            secret_file.to_str().unwrap(),
            "--signed-opening",
            envelope_path.to_str().unwrap(),
        ],
    );
    assert!(
        installed.contains("Installed"),
        "the ceremony must install a fresh slot: {installed}"
    );

    // ── STEP 4 — THE NEW COMMAND. It prints the answer; only the path is echoed.
    step(
        "poa-signal-instance-preview",
        &node_bin,
        &[
            "poa-signal-instance-preview",
            "--data-dir",
            data_dir.to_str().unwrap(),
            "--authority-id",
            &authority_hex,
            "--mission-id",
            &mission_text,
            "--slot",
            &slot_text,
            "--secret-file",
            secret_file.to_str().unwrap(),
            "--player-key",
            &player_key_hex,
            "--output",
            instance_path.to_str().unwrap(),
        ],
    );
    let derived: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&instance_path).expect("instance document"))
            .expect("instance JSON");
    assert_eq!(
        derived["schema"], "POA-SIGNAL-INSTANCE-PREVIEW-V1",
        "step 4 must emit the document step 5 consumes: {derived}"
    );
    assert_eq!(derived["claim"]["mission_id"].as_u64(), Some(MISSION_ID));

    // ── START THE NODE (real consensus loop, real TCP listener) ───────────────
    let state = NodeState::new(&data_dir, vec![]).expect("reopen NodeState");
    let federation_id;
    {
        let mut s = state.write().await;
        s.unlocked = true;
        let node_pk = s.cclerk.public_key();
        let node_seed = s.cclerk.gossip_signing_key().to_bytes();
        let (node_ml_dsa, _) = dregg_federation::frost::MlDsaSigningKey::from_seed(&node_seed);
        s.set_federation_keys_hybrid(vec![node_pk], vec![node_ml_dsa]);
        s.solo_consensus = Some(dregg_federation::solo::SoloConsensusState::new(node_seed));
        federation_id = crate::executor_setup::federation_id_for_executor(&s);
        // ⚑ THE FUNDING, and the live blocker in one line. The player cell must
        // carry value AND commit its ML-DSA half or the claim dies as
        // `InsufficientBalance` / `pq-identity-not-enrolled`. On the live PoA chain
        // there is no way to produce this state: `--deployment-domain` forces
        // `--no-demo-economy`, the manifest tool refuses any funded genesis cell,
        // and `Effect::Mint` needs a fee its zero-balance well cannot pay.
        s.ledger
            .insert_cell(
                dregg_cell::Cell::with_hybrid_balance(
                    player.public_key().0,
                    &player.ml_dsa_public_bytes(),
                    crate::executor_setup::default_token_id(),
                    1_000_000,
                )
                .expect("canonical ML-DSA-65 player identity"),
            )
            .expect("fund the Signal player");
    }
    assert_eq!(
        hex_encode(&federation_id),
        authority_hex,
        "reopening the data dir must reproduce the same node identity, or the head \
         installed in phase 0 belongs to another federation"
    );

    let handle = run_blocklace_sync_with_policy(
        state.clone(),
        0,
        true,
        100,
        10_000,
        50,
        2_000,
        0,
        None,
        dregg_blocklace::finality::ConsensusTimePolicyV1::new(1_700_000_000),
    )
    .await
    .expect("solo blocklace handle");
    state.set_blocklace(handle).await;

    let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
    let app = crate::api::router(state.clone(), true, recorder.handle());
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0")
        .await
        .expect("bind an ephemeral port");
    let port = listener.local_addr().expect("local addr").port();
    tokio::spawn(async move {
        let _ = axum::serve(
            listener,
            app.into_make_service_with_connect_info::<SocketAddr>(),
        )
        .await;
    });
    // The listener is live before the first request: bind happened above, and the
    // accept loop is spawned. Give the runtime one tick to schedule it.
    tokio::time::sleep(Duration::from_millis(200)).await;
    let endpoint = format!("http://127.0.0.1:{port}");

    // The public number BEFORE anything settles — over the same real wire.
    let before: serde_json::Value = reqwest::get(format!("{endpoint}/status"))
        .await
        .expect("status")
        .json()
        .await
        .expect("status json");
    assert_eq!(
        before["latest_height"].as_u64(),
        Some(0),
        "a fresh node has settled no turns: {before}"
    );
    eprintln!(
        "\n  BEFORE  /status latest_height: {}",
        before["latest_height"]
    );

    // ── STEPS 5-6 — THE NEW COMMAND, over real TCP, waiting on the real number.
    let report = step(
        "poa-signal-submit-claim",
        &node_bin,
        &[
            "poa-signal-submit-claim",
            "--endpoint",
            &endpoint,
            "--authority-id",
            &authority_hex,
            "--player-key-file",
            player_key_file.to_str().unwrap(),
            "--claim-file",
            instance_path.to_str().unwrap(),
            "--await-latest-height",
            "1",
            "--await-timeout-secs",
            "90",
        ],
    );
    assert!(
        report.contains("latest_height: 1"),
        "the drill must SETTLE, not merely be accepted: {report}"
    );

    // And the durable authority agrees: one judged transition, and the complete
    // semantic replay re-judges it through native Lean from genesis.
    {
        let s = state.read().await;
        let head = s
            .store
            .load_poa_signal_head(federation_id)
            .expect("PoA head read")
            .expect("advanced PoA head");
        assert_eq!(head.transition_count(), 1, "exactly one judged transition");
        let replay =
            crate::poa_signal_adapter::audit_persisted_signal_semantics(&s.store, federation_id)
                .expect("durable semantic replay must accept the settled history");
        assert_eq!(replay.transition_count, 1);
    }
    eprintln!("\n  REHEARSAL COMPLETE — the ceremony settles when driven by the commands.");
}

fn parse32(hex: &str) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (index, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&hex[index * 2..index * 2 + 2], 16).expect("hex");
    }
    out
}
