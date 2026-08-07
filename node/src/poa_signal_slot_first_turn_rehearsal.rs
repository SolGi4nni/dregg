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
//! 0. dregg-node genesis --player-grant        SUBPROCESS  (no node yet)   ← new
//! 1. dregg-node poa-slot-opening-preview      SUBPROCESS  (node stopped)
//! 2. poa-curator  sign-slot-opening           SUBPROCESS  (CURATOR KEY)
//! 3. dregg-node init-poa-signal-slot          SUBPROCESS  (node stopped)
//! 4. dregg-node poa-signal-instance-preview   SUBPROCESS  (node stopped)
//! 5. dregg-node poa-signal-submit-claim       SUBPROCESS  (node running)
//! 6.   …its --await-latest-height polls GET /status over real TCP
//! ```
//!
//! # ⚑ THE FUNDING, WHICH USED TO BE THE HARNESS LYING TO ITSELF
//!
//! Until 2026-08-07 this drill inserted the player's cell into the ledger by hand,
//! in-process, with `ledger.insert_cell(Cell::with_hybrid_balance(…, 1_000_000))`,
//! and a comment beside it said in as many words that the live chain had no way to
//! produce that state. Which means the drill's own `latest_height: 1` was
//! unreachable on the deployment it was rehearsing: the descriptor issued no value,
//! `execute` refuses any agent below the turn fee, `/api/faucet` is off and has no
//! genesis cell, and `Effect::Mint` needs a fee the zero-balance issuer well cannot
//! pay. The rehearsal passed; the deployment could not have.
//!
//! It is now step 0. The player's identity IS the descriptor's `player_grant` cell,
//! funded by one issuer-move at genesis, and the drill reads `player-grant.key`
//! rather than a constant of its own. So the ledger the ceremony runs against is
//! the ledger `dregg-node genesis` emitted and `reseed_genesis_then_overlay`
//! materialized — the same path `run_node` takes on the live host, with the same
//! `genesis_moves` replay — not a state this file invented.
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
//! * and re-emitting content for a local federation is Lean `Emit` work, out of
//!   scope here.
//!
//! (The third reason used to be that `scripts/poa-devnet-manifest.mjs` refused any
//! PoA genesis that was not exactly the two zero-balance wells. That gate was
//! deliberately widened on 2026-08-07 to permit exactly the funded shape this drill
//! now generates — see `assertGenesisEconomy` there for the recorded reason.)
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
/// The deployment domain the descriptor is scoped to. The same string the live
/// deployment uses, so step 0 exercises the real auxiliary-key derivation.
const DEPLOYMENT_DOMAIN: &str = "pathofangels.network/federation/v1";
/// The genesis grant, in the descriptor's default asset. Deliberately not round:
/// the drill asserts an EXACT balance delta, so a number that happens to equal a
/// fee multiple could hide an off-by-a-fee.
const PLAYER_GRANT: u64 = 100_000;

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
    let curator_secret = work.path().join("curator.secret");
    let curator_pin = work.path().join("curator-pin.json");

    // ── STEP 0 — RE-GENESIS. The descriptor, and the only value on this chain. ─
    //
    // This is the whole point of the funding work: the player identity below is not
    // minted by this file, it is the descriptor's `player_grant` cell, and the only
    // way it holds anything is the one issuer-move `dregg-node genesis` wrote.
    let grant_amount = PLAYER_GRANT.to_string();
    step(
        "genesis (deployment-scoped, no demo economy, funded player grant)",
        &node_bin,
        &[
            "genesis",
            "--validators",
            "1",
            "--deployment-domain",
            DEPLOYMENT_DOMAIN,
            "--no-demo-economy",
            "--player-grant",
            &grant_amount,
            "--output",
            data_dir.to_str().unwrap(),
        ],
    );
    // `run_node` reads `<data-dir>/genesis.json` and `<data-dir>/node.key`; the
    // generator writes the committee's seed as `node-0.key`. Placing it is the
    // operator's step on the real host too (`docs/poa/DEVNET-OPERATOR-KIT.md`).
    std::fs::rename(data_dir.join("node-0.key"), data_dir.join("node.key"))
        .expect("place the validator seed as node.key");
    let genesis: serde_json::Value =
        serde_json::from_slice(&std::fs::read(data_dir.join("genesis.json")).expect("descriptor"))
            .expect("descriptor JSON");

    // The descriptor's OWN claims about its economy, read before any node exists.
    let declared_grant_id = genesis["player_grant"]
        .as_str()
        .expect("a funded PoA descriptor names its player-grant cell")
        .to_owned();
    let declared_column: i64 = genesis["initial_cells"]
        .as_array()
        .expect("initial_cells")
        .iter()
        .map(|cell| cell["balance"].as_i64().expect("signed balance"))
        .sum();
    assert_eq!(
        declared_column, 0,
        "CONSERVATION: the declared value column must sum to zero — an issuer-move \
         genesis whose books do not close is minting from nowhere: {genesis}"
    );
    assert_eq!(
        genesis["genesis_moves"].as_array().map(Vec::len),
        Some(1),
        "the funded descriptor carries exactly one issuer-move"
    );

    // THE PLAYER IS THE GRANT CELL. Its seed comes off the generated bundle, not
    // out of a constant in this file — so if the derivation, the asset, or the
    // ML-DSA commitment were wrong, the ceremony below would fail rather than run
    // against a cell the harness had arranged to exist.
    let player_key_file = data_dir.join(crate::genesis::PLAYER_GRANT_KEY_FILE);
    let player_seed: [u8; 32] = std::fs::read(&player_key_file)
        .expect("the generated bundle carries the player-grant seed")
        .try_into()
        .expect("a 32-byte Ed25519 seed");
    let player = dregg_sdk::AgentCipherclerk::from_key_bytes(Zeroizing::new(player_seed));
    let player_key_hex = hex_encode(&player.public_key().0);
    let player_cell = dregg_sdk::poa_signal::signal_player_cell(&player.public_key().0);
    assert_eq!(
        hex_encode(&player_cell.0),
        declared_grant_id,
        "the cell the Signal perimeter derives for this player must BE the descriptor's \
         funded grant cell; if these differ the grant funds a cell nobody can act as"
    );
    // The seed file the submit-claim command reads must be hex, as an operator's is.
    let player_key_hex_file = work.path().join("player.key");
    std::fs::write(&player_key_hex_file, hex_encode(&player_seed)).expect("player key");

    // ── the curator draws its key. Off the node, as it must be. ──────────────
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
    // The node identity this drill boots must BE the descriptor's committee. If it
    // is not, everything below runs against a federation the descriptor does not
    // describe — which is exactly the fiction the old in-process funding hid.
    assert_eq!(
        authority_hex,
        genesis["federation_id"].as_str().unwrap(),
        "the placed node.key must reproduce the descriptor's committee-derived federation id"
    );

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
    let issuer_well_id;
    let fee_well_id;
    {
        let mut s = state.write().await;
        s.unlocked = true;
        let node_pk = s.cclerk.public_key();
        let node_seed = s.cclerk.gossip_signing_key().to_bytes();
        let (node_ml_dsa, _) = dregg_federation::frost::MlDsaSigningKey::from_seed(&node_seed);
        s.set_federation_keys_hybrid(vec![node_pk], vec![node_ml_dsa]);
        s.solo_consensus = Some(dregg_federation::solo::SoloConsensusState::new(node_seed));
        federation_id = crate::executor_setup::federation_id_for_executor(&s);

        // ⚑ THE FUNDING — and there is nothing here that funds anything. The
        // ledger comes out of the DESCRIPTOR, through the same reconstruction
        // `run_node` runs on the live host: materialize every `initial_cells` entry
        // VALUE-EMPTY, then replay the `genesis_moves` exactly once. The player's
        // balance is the outcome of an issuer-move, not an insert.
        let stats = crate::reseed_genesis_then_overlay(&genesis, &mut s.ledger, &[]);
        assert_eq!(
            stats.invalid, 0,
            "every declared post-seed balance must be the exact issuer-move outcome"
        );

        // The wells, exactly as `run_node` picks them up — LOAD-BEARING for
        // conservation: without the fee well configured, a fee BURNS and the value
        // column silently stops summing to zero the moment a turn settles.
        issuer_well_id = dregg_cell::CellId(parse32(
            genesis["issuer_well"].as_str().expect("issuer_well"),
        ));
        fee_well_id = dregg_cell::CellId(parse32(genesis["fee_well"].as_str().expect("fee_well")));
        s.fee_well = Some(fee_well_id);
        let well_asset = s
            .ledger
            .get(&issuer_well_id)
            .map(|cell| *cell.asset().as_bytes())
            .expect("the issuer well materialized");
        s.issuer_wells.push((well_asset, issuer_well_id));
    }
    assert_eq!(
        hex_encode(&federation_id),
        authority_hex,
        "reopening the data dir must reproduce the same node identity, or the head \
         installed in phase 0 belongs to another federation"
    );

    // The genesis economy, as the LEDGER holds it — the numbers the executor will
    // read, not the numbers the descriptor declared.
    let balance_of = |ledger: &dregg_cell::Ledger, id: &dregg_cell::CellId| -> i64 {
        ledger.get(id).map(|cell| cell.state.balance()).unwrap_or(0)
    };
    let (grant_before, column_before) = {
        let s = state.read().await;
        let column: i128 = s
            .ledger
            .iter()
            .map(|(_, cell)| cell.state.balance() as i128)
            .sum();
        (balance_of(&s.ledger, &player_cell), column)
    };
    assert_eq!(
        grant_before, PLAYER_GRANT as i64,
        "the player-grant cell must hold exactly the issuer-move amount before any turn"
    );
    assert_eq!(
        column_before, 0,
        "CONSERVATION at boot: the materialized value column must sum to zero"
    );
    eprintln!(
        "\n  GENESIS  player-grant cell {} holds {grant_before}; value column Σ = {column_before}",
        &declared_grant_id[..16]
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
            player_key_hex_file.to_str().unwrap(),
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

    // ── VALUE MOVED. Not "a test passed". ────────────────────────────────────
    //
    // `latest_height: 1` says a block was produced. It does NOT say the player paid
    // for it: a fee that burned, a fee charged to nobody, or a fee of zero would all
    // leave the height at 1. The point of the genesis grant is that a real balance
    // went down by a real fee and the same amount arrived somewhere real, so that is
    // what is asserted — with the fee taken from the SDK's canonical pricing, never
    // from the observed delta (an assertion that derives its expectation from the
    // measurement cannot fail).
    let claim_fee = dregg_sdk::poa_signal::signal_claim_fee_v1();
    let (grant_after, fee_well_after, column_after) = {
        let s = state.read().await;
        let column: i128 = s
            .ledger
            .iter()
            .map(|(_, cell)| cell.state.balance() as i128)
            .sum();
        (
            balance_of(&s.ledger, &player_cell),
            balance_of(&s.ledger, &fee_well_id),
            column,
        )
    };
    eprintln!(
        "\n  SETTLED  player-grant {grant_before} → {grant_after}  (Δ = -{})\n           \
         fee well 0 → {fee_well_after}   (the canonical Signal claim fee is {claim_fee})\n           \
         value column Σ = {column_after}",
        grant_before - grant_after
    );
    assert_eq!(
        grant_before - grant_after,
        claim_fee as i64,
        "the settled turn must be PAID FOR out of the genesis grant, by exactly the \
         canonical Signal claim fee"
    );
    assert_eq!(
        fee_well_after, claim_fee as i64,
        "the fee is a MOVE to the fee well, not a burn; a burnt fee would leave the \
         value column short by exactly the fee"
    );
    assert_eq!(
        column_after, 0,
        "CONSERVATION after the turn: the value column must still sum to zero"
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

/// THE OTHER POLE: an UNDERFUNDED player is refused, and the refusal NAMES THE FEE.
///
/// A funded player settling is only half the property. The half that decides
/// whether an operator can act on a failure is what an underfunded one sees, and a
/// deployment refusing every claim with something shapeless is a deployment nobody
/// can debug. There are two refusals and they are at different distances:
///
/// * `dregg-node genesis` refuses the underfunded grant OUTRIGHT, before a chain
///   exists — the cheap one, and the only one that costs nothing to act on;
/// * the executor refuses the turn with `InsufficientBalance { required, available }`,
///   whose `Display` is `insufficient balance on cell …: need N, have M`.
///
/// Both are checked here: the CLI one as a real process, the runtime one against
/// the real executor over a real ledger, so the numbers are the deployed pricing
/// rather than a restatement.
#[tokio::test]
#[ignore = "runs the built dregg-node binary; build it first (see module docs)"]
async fn an_underfunded_player_is_refused_with_the_fee_named() {
    let _ = crate::install_mldsa_verified_keygen_core_real();
    let node_bin = binary("dregg-node");
    let work = tempfile::tempdir().expect("tempdir");
    let claim_fee = dregg_sdk::poa_signal::signal_claim_fee_v1();

    // ── POLE 1: the operator types a grant that cannot buy one turn. ─────────
    let short = (claim_fee - 1).to_string();
    let out = std::process::Command::new(&node_bin)
        .args([
            "genesis",
            "--validators",
            "1",
            "--deployment-domain",
            DEPLOYMENT_DOMAIN,
            "--no-demo-economy",
            "--player-grant",
            &short,
            "--output",
            work.path().join("short").to_str().unwrap(),
        ])
        .output()
        .expect("spawn dregg-node genesis");
    let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
    assert!(
        !out.status.success() || stderr.contains("below the Path of Angels Signal claim fee"),
        "an underfunded grant must be REFUSED at genesis: {stderr}"
    );
    assert!(
        stderr.contains(&claim_fee.to_string()) && stderr.contains(&short),
        "the refusal must name BOTH the fee and what was offered, or the operator \
         cannot act on it: {stderr}"
    );
    assert!(
        !work.path().join("short").join("genesis.json").exists(),
        "a refused genesis must leave no descriptor behind"
    );
    eprintln!("\n  REFUSED (genesis): {}", stderr.trim());

    // ── POLE 2: a hybrid player cell that exists but cannot cover the fee. ───
    let player = dregg_sdk::AgentCipherclerk::from_key_bytes(Zeroizing::new([0x4du8; 32]));
    let underfunded = claim_fee - 1;
    let mut ledger = dregg_cell::Ledger::new();
    ledger
        .insert_cell(
            dregg_cell::Cell::with_hybrid_balance(
                player.public_key().0,
                &player.ml_dsa_public_bytes(),
                crate::executor_setup::default_token_id(),
                underfunded as i64,
            )
            .expect("canonical ML-DSA-65 identity"),
        )
        .expect("insert the underfunded player");
    let claim = dregg_sdk::poa_signal::SignalClaimV1::new(
        MISSION_ID,
        dregg_sdk::poa_signal::SignalCode::new(1, 2, 3).unwrap(),
    )
    .unwrap();
    let turn = dregg_sdk::poa_signal::signal_claim_turn(&player.public_key().0, 0, None, claim);
    let error = dregg_turn::TurnExecutor::new(dregg_turn::ComputronCosts::default())
        .validate_without_apply(&turn, &ledger)
        .expect_err("an underfunded player must be REFUSED");
    let rendered = error.to_string();
    assert!(
        matches!(error, dregg_turn::TurnError::InsufficientBalance { required, available, .. }
            if required == claim_fee && available == underfunded as i64),
        "the refusal must carry the fee and the balance, not a generic admission error: {error:?}"
    );
    assert!(
        rendered.contains(&format!("need {claim_fee}"))
            && rendered.contains(&format!("have {underfunded}")),
        "the rendered diagnosis must name the fee: {rendered}"
    );
    eprintln!("  REFUSED (runtime): {rendered}");
}

fn parse32(hex: &str) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (index, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&hex[index * 2..index * 2 + 2], 16).expect("hex");
    }
    out
}
