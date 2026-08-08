use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

#[cfg(unix)]
use std::os::unix::fs::{MetadataExt, symlink};

use serde_json::json;
use sha2::{Digest, Sha256};

fn binary() -> &'static str {
    env!("CARGO_BIN_EXE_poa-curator")
}

#[test]
fn promotion_inbox_fails_closed_on_missing_authority_and_content_artifacts() {
    let output = Command::new(binary())
        .args([
            "promotion-inbox",
            "--bundle",
            "caller-supplied.json",
            "--manifest",
            "catalog.json",
            "--deployment",
            "deployment.json",
            "--pin",
            "curator-pin.json",
            "--signature",
            "content-epoch.json",
            "--epoch",
            "1",
            "--counter",
            "1",
        ])
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    let error = String::from_utf8_lossy(&output.stderr);
    assert!(error.contains("poa-curator:"));
    assert!(error.contains("No such file") || error.contains("not found"));
}

#[test]
fn keygen_is_mode_safe_and_refuses_overwrite() {
    let temp = tempfile::tempdir().unwrap();
    let secret = temp.path().join("development-curator.key");
    let pin = temp.path().join("curator-key.json");
    let first = Command::new(binary())
        .args(["keygen", "--secret"])
        .arg(&secret)
        .arg("--pin")
        .arg(&pin)
        .output()
        .unwrap();
    assert!(
        first.status.success(),
        "{}",
        String::from_utf8_lossy(&first.stderr)
    );
    let secret_before = fs::read(&secret).unwrap();
    let pin_before = fs::read(&pin).unwrap();
    assert_eq!(secret_before.len(), 32);
    assert!(!String::from_utf8_lossy(&pin_before).contains(&hex(&secret_before)));
    #[cfg(unix)]
    assert_eq!(fs::metadata(&secret).unwrap().mode() & 0o777, 0o600);

    let second = Command::new(binary())
        .args(["keygen", "--secret"])
        .arg(&secret)
        .arg("--pin")
        .arg(&pin)
        .output()
        .unwrap();
    assert!(!second.status.success());
    assert!(String::from_utf8_lossy(&second.stderr).contains("refusing to overwrite"));
    assert_eq!(fs::read(&secret).unwrap(), secret_before);
    assert_eq!(fs::read(&pin).unwrap(), pin_before);
}

#[cfg(unix)]
#[test]
fn keygen_refuses_a_preexisting_symlink_output() {
    let temp = tempfile::tempdir().unwrap();
    let victim = temp.path().join("victim");
    fs::write(&victim, b"do not touch").unwrap();
    let secret = temp.path().join("development-curator.key");
    let pin = temp.path().join("curator-key.json");
    symlink(&victim, &secret).unwrap();

    let output = Command::new(binary())
        .args(["keygen", "--secret"])
        .arg(&secret)
        .arg("--pin")
        .arg(&pin)
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert_eq!(fs::read(&victim).unwrap(), b"do not touch");
    assert!(!pin.exists());
}

/// The deployment `poa/deployments/epoch-1/` points at, pinned HERE rather than only
/// inside the golden file.
///
/// ⚠ Why these are duplicated out of the snapshot. The golden went stale, and the
/// delta was not new content: it was a DIFFERENT DEPLOYMENT — federation
/// `4ea83e8e…` → `70b7fa4c…`, deployment `d933b11b…` → `4db835cc…` — sitting in the
/// middle of an otherwise ordinary mission diff. A lane refused to regenerate it
/// rather than bless that silently, and was right to. Regenerating a golden must not
/// be able to move the deployment identity, so the identity is a constant the
/// regeneration path cannot touch and a change to it fails with its own name.
const EPOCH_ONE_FEDERATION_ID: &str =
    "70b7fa4cfbc3921bef2e1ddb1a42869c8dcef27539179c9cbdf6a6e6b1d07c1b";
const EPOCH_ONE_DEPLOYMENT_ID: &str =
    "4db835cc36cd0d3b722e742334dc1dde9557601fe1334c7499ab023de4d6d45d";

#[test]
fn unsigned_epoch_preview_matches_the_exact_checked_in_snapshot() {
    let repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let snapshot =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/snapshots/epoch-1-unsigned.json");
    let output = Command::new(binary())
        .args(["preview-epoch", "--manifest"])
        .arg(repo.join("poa/artifacts/poag1/manifest.json"))
        .arg("--deployment")
        .arg(repo.join("poa/deployments/epoch-1/poa-devnet.json"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let rendered = String::from_utf8(output.stdout).unwrap();

    // Checked BEFORE any regeneration, and never regenerated: an identity move must
    // fail by name, in update mode as much as in check mode.
    let parsed: serde_json::Value = serde_json::from_str(&rendered).unwrap();
    assert_eq!(
        parsed["federation_id"], EPOCH_ONE_FEDERATION_ID,
        "epoch-1 preview names a different federation; this is a deployment identity \
         change, not a content change, and it does not belong in a golden regeneration"
    );
    assert_eq!(
        parsed["deployment_id"], EPOCH_ONE_DEPLOYMENT_ID,
        "epoch-1 preview names a different deployment; this is a deployment identity \
         change, not a content change, and it does not belong in a golden regeneration"
    );

    // Regeneration is one command, and it REFUSES to also report success — a mode
    // that writes the file and then compares it against itself is a test that has
    // stopped testing.
    if std::env::var_os("POA_CURATOR_UPDATE_SNAPSHOTS").is_some() {
        fs::write(&snapshot, rendered.as_bytes()).unwrap();
        panic!(
            "snapshot regenerated at {}; re-run WITHOUT POA_CURATOR_UPDATE_SNAPSHOTS to verify it",
            snapshot.display()
        );
    }
    assert_eq!(rendered, fs::read_to_string(&snapshot).unwrap());
}

#[test]
fn content_sign_and_verify_cli_roundtrip() {
    let temp = tempfile::tempdir().unwrap();
    let (manifest, deployment) = write_bundle(temp.path());
    let secret = temp.path().join("development-curator.key");
    let pin = temp.path().join("curator-key.json");
    let signature = temp.path().join("manifest.sig.json");
    assert!(
        Command::new(binary())
            .args(["keygen", "--secret"])
            .arg(&secret)
            .arg("--pin")
            .arg(&pin)
            .status()
            .unwrap()
            .success()
    );
    assert!(
        Command::new(binary())
            .args(["sign-content", "--secret"])
            .arg(&secret)
            .arg("--pin")
            .arg(&pin)
            .arg("--manifest")
            .arg(&manifest)
            .arg("--deployment")
            .arg(&deployment)
            .args(["--epoch", "2", "--counter", "1", "--output"])
            .arg(&signature)
            .status()
            .unwrap()
            .success()
    );
    let verified = Command::new(binary())
        .args(["verify-content", "--pin"])
        .arg(&pin)
        .arg("--manifest")
        .arg(&manifest)
        .arg("--deployment")
        .arg(&deployment)
        .args(["--epoch", "2", "--counter", "1", "--signature"])
        .arg(&signature)
        .output()
        .unwrap();
    assert!(
        verified.status.success(),
        "{}",
        String::from_utf8_lossy(&verified.stderr)
    );
    assert!(String::from_utf8_lossy(&verified.stdout).contains("activation sha256:"));

    let preview = Command::new(binary())
        .args(["preview-epoch", "--manifest"])
        .arg(&manifest)
        .arg("--deployment")
        .arg(&deployment)
        .arg("--pin")
        .arg(&pin)
        .arg("--signature")
        .arg(&signature)
        .args(["--epoch", "2", "--counter", "1"])
        .output()
        .unwrap();
    assert!(
        preview.status.success(),
        "{}",
        String::from_utf8_lossy(&preview.stderr)
    );
    let preview: serde_json::Value = serde_json::from_slice(&preview.stdout).unwrap();
    assert_eq!(preview["signature_status"], "valid");
    assert_eq!(preview["signature_epoch"], 2);
    assert_eq!(preview["signature_counter"], 1);
    assert_eq!(
        preview["notice"],
        "SIGNATURE VERIFIED: this review preview is not a Lean mission activation"
    );

    let rollback = Command::new(binary())
        .args(["verify-content", "--pin"])
        .arg(&pin)
        .arg("--manifest")
        .arg(&manifest)
        .arg("--deployment")
        .arg(&deployment)
        .args(["--epoch", "1", "--counter", "1", "--signature"])
        .arg(&signature)
        .output()
        .unwrap();
    assert!(!rollback.status.success());
}

#[test]
fn companion_sign_and_verify_cli_is_bound_to_content_and_refuses_overwrite() {
    let repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let manifest = repo.join("poa/artifacts/poag1/manifest.json");
    let deployment = repo.join("poa/deployments/epoch-1/poa-devnet.json");
    let temp = tempfile::tempdir().unwrap();
    let secret = temp.path().join("development-curator.key");
    let pin = temp.path().join("curator-key.json");
    let content_signature = temp.path().join("manifest.sig.json");
    let draft = temp.path().join("episode-1-draft.json");
    let output = temp.path().join("AbCdEfGhI01.json");
    assert!(
        Command::new(binary())
            .args(["keygen", "--secret"])
            .arg(&secret)
            .arg("--pin")
            .arg(&pin)
            .status()
            .unwrap()
            .success()
    );
    assert!(
        Command::new(binary())
            .args(["sign-content", "--secret"])
            .arg(&secret)
            .arg("--pin")
            .arg(&pin)
            .arg("--manifest")
            .arg(&manifest)
            .arg("--deployment")
            .arg(&deployment)
            .args(["--epoch", "1", "--counter", "4", "--output"])
            .arg(&content_signature)
            .status()
            .unwrap()
            .success()
    );
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_secs();
    let manifest_digest = format!(
        "sha256:{}",
        hex(&Sha256::digest(fs::read(&manifest).unwrap()))
    );
    // ⚠ The catalog pin is DERIVED from the authenticated manifest, not copied into
    // the fixture. It used to be a literal `bytes: 5447` and a literal sha256, and
    // `validate_experience` compares the asset against `pin.bytes`/`pin.sha256` — so
    // every re-emit of the bundle broke this test in a way that reads like a
    // signing bug. Enrolling a fourth game re-emits the catalog again; deriving it
    // means that is no longer an edit here.
    let manifest_value: serde_json::Value =
        serde_json::from_slice(&fs::read(&manifest).unwrap()).unwrap();
    let catalog_pin = manifest_value["artifacts"]
        .as_array()
        .unwrap()
        .iter()
        .find(|pin| pin["path"] == "catalog.json")
        .expect("the authenticated POAG1 manifest pins catalog.json");
    let catalog_bytes = catalog_pin["bytes"].as_u64().unwrap();
    let catalog_sha = catalog_pin["sha256"]
        .as_str()
        .unwrap()
        .strip_prefix("sha256:")
        .expect("POAG1 pins are canonical sha256: values")
        .to_owned();
    fs::write(
        &draft,
        serde_json::to_vec_pretty(&json!({
            "schema": "poa-companion/v3",
            "contentEpoch": 1,
            "contentCounter": 4,
            "sequence": 1,
            "poaOrigin": "https://beta.pathofangels.network",
            // ⚠ THE SAME STALENESS AS THE GOLDEN, IN A THIRD COPY. These were the
            // literal old ids, while this test binds against the REAL
            // `poa/deployments/epoch-1/poa-devnet.json`, which moved to 70b7fa4c /
            // 4db835cc. So `validate` refused with "route is not bound to the
            // verified PoA deployment" and had been doing so since the identity
            // changed. Named from the constants now, so the identity has ONE source
            // in this file and a fourth copy cannot drift in behind it.
            //
            // This does not soften the binding check: `companion.rs`'s
            // `v3_signature_and_content_ceremony_refuse_every_scope_substitution`
            // derives the correct ids and substitutes "aa"*32 into each, asserting
            // refusal. That is where the check is proved to have teeth; this is the
            // happy path and was only failing because its fixture was stale.
            "federationId": EPOCH_ONE_FEDERATION_ID,
            "deploymentId": EPOCH_ONE_DEPLOYMENT_ID,
            "contentPackDigest": manifest_digest,
            "context": {
                "platform": "youtube",
                "videoId": "AbCdEfGhI01",
                "channelId": "UC_PathOfAngels"
            },
            "experience": {
                "id": "episode-1",
                "title": "Path of Angels field dispatch",
                "episode": "Episode 1",
                "betaUrl": "https://beta.pathofangels.network/?episode=1",
                "contentAssets": [{
                    "path": "catalog.json",
                    "url": "https://beta.pathofangels.network/artifacts/poag1/catalog.json",
                    "mediaType": "application/json",
                    "bytes": catalog_bytes,
                    "sha256": catalog_sha
                }],
                "actions": {
                    "mission": {
                        "label": "Open field terminal",
                        "betaUrl": "https://beta.pathofangels.network/?station=field"
                    }
                }
            },
            "issuedAt": now,
            "expiresAt": now + 3600
        }))
        .unwrap(),
    )
    .unwrap();
    let sign = Command::new(binary())
        .args(["sign-companion", "--secret"])
        .arg(&secret)
        .arg("--pin")
        .arg(&pin)
        .arg("--manifest")
        .arg(&manifest)
        .arg("--deployment")
        .arg(&deployment)
        .arg("--content-signature")
        .arg(&content_signature)
        .args(["--content-epoch", "1", "--content-counter", "4", "--draft"])
        .arg(&draft)
        .arg("--output")
        .arg(&output)
        .output()
        .unwrap();
    assert!(
        sign.status.success(),
        "{}",
        String::from_utf8_lossy(&sign.stderr)
    );
    let before = fs::read(&output).unwrap();

    let verify = Command::new(binary())
        .args(["verify-companion", "--pin"])
        .arg(&pin)
        .arg("--manifest")
        .arg(&manifest)
        .arg("--deployment")
        .arg(&deployment)
        .arg("--content-signature")
        .arg(&content_signature)
        .args(["--content-epoch", "1", "--content-counter", "4", "--input"])
        .arg(&output)
        .output()
        .unwrap();
    assert!(
        verify.status.success(),
        "{}",
        String::from_utf8_lossy(&verify.stderr)
    );
    assert!(String::from_utf8_lossy(&verify.stdout).contains("sequence 1"));

    let overwrite = Command::new(binary())
        .args(["sign-companion", "--secret"])
        .arg(&secret)
        .arg("--pin")
        .arg(&pin)
        .arg("--manifest")
        .arg(&manifest)
        .arg("--deployment")
        .arg(&deployment)
        .arg("--content-signature")
        .arg(&content_signature)
        .args(["--content-epoch", "1", "--content-counter", "4", "--draft"])
        .arg(&draft)
        .arg("--output")
        .arg(&output)
        .output()
        .unwrap();
    assert!(!overwrite.status.success());
    assert!(String::from_utf8_lossy(&overwrite.stderr).contains("refusing to overwrite"));
    assert_eq!(fs::read(&output).unwrap(), before);
}

#[test]
fn preview_refuses_partial_verification_tampered_bytes_and_wrong_counter() {
    let temp = tempfile::tempdir().unwrap();
    let (manifest, deployment) = write_bundle(temp.path());
    let partial = Command::new(binary())
        .args(["preview-epoch", "--manifest"])
        .arg(&manifest)
        .arg("--deployment")
        .arg(&deployment)
        .args(["--pin", "not-read.json"])
        .output()
        .unwrap();
    assert!(!partial.status.success());
    assert!(partial.stdout.is_empty());
    assert!(String::from_utf8_lossy(&partial.stderr).contains(
        "signature verification requires --pin, --signature, --epoch, and --counter together"
    ));

    let game_path = temp.path().join("games/signal-triangulation.json");
    let mut tampered_game = fs::read(&game_path).unwrap();
    tampered_game.push(b'\n');
    fs::write(&game_path, tampered_game).unwrap();
    let tampered = Command::new(binary())
        .args(["preview-epoch", "--manifest"])
        .arg(&manifest)
        .arg("--deployment")
        .arg(&deployment)
        .output()
        .unwrap();
    assert!(!tampered.status.success());
    assert!(tampered.stdout.is_empty());

    let (manifest, deployment) = write_bundle(temp.path());
    let secret = temp.path().join("preview-curator.key");
    let pin = temp.path().join("preview-curator-pin.json");
    let signature = temp.path().join("preview-manifest.sig.json");
    assert!(
        Command::new(binary())
            .args(["keygen", "--secret"])
            .arg(&secret)
            .arg("--pin")
            .arg(&pin)
            .status()
            .unwrap()
            .success()
    );
    assert!(
        Command::new(binary())
            .args(["sign-content", "--secret"])
            .arg(&secret)
            .arg("--pin")
            .arg(&pin)
            .arg("--manifest")
            .arg(&manifest)
            .arg("--deployment")
            .arg(&deployment)
            .args(["--epoch", "2", "--counter", "1", "--output"])
            .arg(&signature)
            .status()
            .unwrap()
            .success()
    );
    let wrong_counter = Command::new(binary())
        .args(["preview-epoch", "--manifest"])
        .arg(&manifest)
        .arg("--deployment")
        .arg(&deployment)
        .arg("--pin")
        .arg(&pin)
        .arg("--signature")
        .arg(&signature)
        .args(["--epoch", "2", "--counter", "2"])
        .output()
        .unwrap();
    assert!(!wrong_counter.status.success());
    assert!(wrong_counter.stdout.is_empty());
}

fn write_bundle(root: &Path) -> (PathBuf, PathBuf) {
    fs::create_dir_all(root.join("games")).unwrap();
    let schema = serde_json::to_vec(&json!({
        "format":"POAG1-SCHEMA", "schema_version":1,
        "contract":{
            "manifest_required":["format","schema_version","source_digest","authority","artifacts"],
            "artifact_pin_required":["path","media_type","bytes","sha256","fnv1a64"],
            "source_digest_pattern":"^sha256:[0-9a-f]{64}$",
            "artifact_sha256_pattern":"^sha256:[0-9a-f]{64}$",
            "bytes32_pattern":"^[0-9a-f]{64}$",
            "fnv1a64_pattern":"^[0-9a-f]{16}$",
            "content_root":{"algorithm":"sha256","domain":"path-of-angels/content-root/v1\0","framing":"file_count_be64 || (path_len_be64 || path_utf8 || content_len_be64 || content_bytes)*","entry_order":"path_ascending","paths":["games/signal-triangulation.json"]},
            "relic_namespace":{"scheme":"per-mission-block","block_width":16,
                "owner":"relic_id / block_width == mission_id","cross_mission":"disjoint-by-construction",
                "authored_in":"Dregg2.Games.PathOfAngels.RelicNamespace","violation":"refuse"},
            "activation_digest":{"algorithm":"sha256","domain":"pathofangels.network/activation-digest/v1\0","framing":"schema_len_be64 || schema_utf8 || manifest_sha256_raw32 || curator_pubkey_raw32 || content_epoch_be64 || counter_be64 || signature_raw64","location":"detached verified activation; excluded from manifest preimage"},
            "slot_opening":{"required":["slot","mission_id","commitment","curator_pubkey","signature"],
                "commitment":{"algorithm":"poseidon2-babybear-w16","domain":"POAC","preimage":"domain || slot || slot_secret","binding_bits":124},
                "opened_after_close":["slot","slot_secret"],
                "verify":"commit(slot_secret, slot) == commitment","missing_opening":"refuse"},
            "run_instance":{"derivation_module":"Dregg2.Games.PathOfAngels.HiddenInstance",
                "function":"runSeedFor(draw, mission)",
                "preimage":"POAD || purpose || slot || mission_id || epoch || slot_secret || federation_id || content_session || player_key",
                "purposes":{"judged":1,"practice":2},"published_anywhere":false,"operator_knows_instance":true,
                "practice":{"seed":"client-chosen","scored":false,"transcript_field":"mode","judge_accepts":false}},
            "unknown_fields":"reject","unknown_artifacts":"reject"
        }
    })).unwrap();
    let game = serde_json::to_vec(&json!({
        "format":"POAG1-GAME", "schema_version":1,
        "game_id":"signal-triangulation", "ruleset":"signal-v1",
        "engine_module":"Dregg2.Games.PathOfAngels.SignalTriangulation",
        "action_limit":5, "definition":{}
    }))
    .unwrap();
    let source = format!("sha256:{}", "11".repeat(32));
    let game_digest = sha(&game);
    let mut root_preimage = b"path-of-angels/content-root/v1\0".to_vec();
    root_preimage.extend_from_slice(&1u64.to_be_bytes());
    frame(&mut root_preimage, b"games/signal-triangulation.json");
    frame(&mut root_preimage, &game);
    let content_root = sha(&root_preimage);
    let catalog = serde_json::to_vec(&json!({
        "format":"POAG1-CATALOG", "schema_version":1,
        "missions":[{
            "mission_id":7,"title":"Signal Triangulation","engine_module":"Dregg2.Games.PathOfAngels.SignalTriangulation",
            "ruleset":"signal-v1","reward_class":"non-economic-demo","action_limit":5,"privacy_grade":"public",
            "ballot_regime":"none","epoch":2,"federation_id":"33".repeat(32),"content_root":content_root,
            "activation":{"state":"detached-signature-required","digest_source":"POA-CONTENT-EPOCH-SIGNATURE-V1"},
            "content_session":"55".repeat(32),
            "instance":{"binding":"per-run-hidden-draw","disclosure":"oracle-only",
                "derivation_module":"Dregg2.Games.PathOfAngels.HiddenInstance",
                "commitment_published_in":"slot-opening"},
            "budget":{"intel":0,"supplies":0,"cohesion":0,"influence":0,"score":0,"relics":0},"allowed_relics":[],
            "descriptor_path":"games/signal-triangulation.json",
            "allowed_beta_discoveries":[{"mission_id":7,"artifact_id":447,"source_digest":source,"content_digest":game_digest}]
        }], "fixtures":[]
    })).unwrap();
    let files = [
        ("schema.json", "application/schema+json", schema),
        ("catalog.json", "application/json", catalog),
        ("games/signal-triangulation.json", "application/json", game),
    ];
    let mut pins = Vec::new();
    for (path, media, bytes) in &files {
        fs::write(root.join(path), bytes).unwrap();
        pins.push(json!({"path":path,"media_type":media,"bytes":bytes.len(),"sha256":sha(bytes),"fnv1a64":fnv(bytes)}));
    }
    let manifest = root.join("manifest.json");
    fs::write(&manifest, serde_json::to_vec(&json!({"format":"POAG1","schema_version":1,"source_digest":source,"authority":"Dregg2.Games.PathOfAngels","artifacts":pins})).unwrap()).unwrap();
    let deployment = root.join("poa-devnet.json");
    fs::write(&deployment, serde_json::to_vec(&json!({"schema":"dregg-poa-devnet-manifest-v1","deployment_domain":"pathofangels.network/federation/v1","deployment_id":"77".repeat(32),"federation_id":"33".repeat(32),"committee_epoch":0,"threshold":1,"genesis_sha256":"88".repeat(32),"descriptor":"bundle/genesis.json","policy":serde_json::from_str::<serde_json::Value>(poa_curator::POA_PRODUCTION_POLICY_ZERO_ISSUANCE).unwrap(),"nodes":[]})).unwrap()).unwrap();
    (manifest, deployment)
}

fn frame(output: &mut Vec<u8>, bytes: &[u8]) {
    output.extend_from_slice(&(bytes.len() as u64).to_be_bytes());
    output.extend_from_slice(bytes);
}
fn sha(bytes: &[u8]) -> String {
    format!("sha256:{}", hex(&Sha256::digest(bytes)))
}
fn fnv(bytes: &[u8]) -> String {
    let mut h = 0xcbf29ce484222325u64;
    for b in bytes {
        h ^= u64::from(*b);
        h = h.wrapping_mul(0x100000001b3);
    }
    format!("{h:016x}")
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        output.push(DIGITS[(byte >> 4) as usize] as char);
        output.push(DIGITS[(byte & 0x0f) as usize] as char);
    }
    output
}
