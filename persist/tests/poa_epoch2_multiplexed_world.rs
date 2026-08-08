//! The epoch-2 MULTIPLEXED world, replayed against the real store and the real Lean.
//!
//! # The wound
//!
//! `poa_world_activation.rs:23` keys the active head at the single string `"active"`,
//! and `audit_tables_in` refuses a table with more than one head — so a store has
//! exactly ONE active world, and `install_poa_activated_content_v1` keys its manifest
//! row by the FULL five-field world tuple. Both shipped epoch-1 worlds (galley and
//! night-watch) declare `content_epoch: 1` on the same federation, and a non-bootstrap
//! `.advance` must carry `contentEpoch = prev + 1`. Mounting night-watch as its own
//! epoch-2 world therefore moves the head off the galley's world, after which
//! `prepare_active_poa_galley_policy_v1_in` finds no row and refuses — the "GALLEY
//! SEALED" 503.
//!
//! # What is proved here, and what is proved in Lean
//!
//! * `both_organs_are_served_from_one_epoch2_activation` — the store fact. One signed
//!   `.advance` off the real epoch-1 galley world, one manifest install, and BOTH the
//!   galley policy (through `load_authenticated_poa_galley_policy_v1`, i.e. the real
//!   `dregg_poa_activated_content_authorize`) AND the night-watch config (through the
//!   real `dregg_poa_night_watch_campaign_judge`) resolve — plus a clean reopen audit,
//!   which is where the single-head invariant is enforced.
//! * `the_single_component_epoch2_world_evicts_the_galley` — the failure the
//!   multiplexed world prevents, exhibited on the same store shape.
//! * `the_shipped_multiplexed_manifest_installs_and_serves_the_galley` — the SHIPPED
//!   bytes in `poa/artifacts/angels-epoch-2/`, not a fixture.
//!
//! ⚠ The end-to-end judge runs against the REHEARSAL instance, and can only ever run
//! against it: the shipped world's slot secret is curator-held and outside every
//! repository by design, so no repository test can produce an `Activation` for it.
//! The shipped world's night-watch side is decided in Lean over the exact shipped
//! bytes (`AngelsEpoch2World.one_epoch2_world_serves_both_organs`), which is the
//! `authorizeCampaignConfigForWorld?` gate itself. The two fixtures differ in exactly
//! one field — the slot commitment — and nothing else.
//!
//! Every JSON byte here is read from an artifact emitted by
//! `Dregg2.Games.PathOfAngels.AngelsEpoch2WorldEmitMain`. This file authors no
//! manifest, no policy and no config: a second spelling of any of them would be the
//! twin the whole seam exists to avoid.

use std::path::{Path, PathBuf};

use dregg_lean_ffi::poa_activated_content_ffi::poa_activated_content_runtime_available;
use dregg_lean_ffi::poa_night_watch_ffi::{
    PoaNightWatchVerdict, judge_poa_night_watch_campaign, poa_night_watch_campaign_available,
};
use dregg_lean_ffi::poa_world_activation_ffi::poa_world_activation_available;
use dregg_persist::poa_world_activation::PoaWorldActivationInstallStatusV1;
use dregg_persist::{
    PersistentStore, PoaActivatedContentInstallStatusV1, PoaWorldActivationKindV1,
    PoaWorldActivationStatementV1, PoaWorldIdentityV2, SignedPoaWorldActivationEnvelopeV1,
};
use ed25519_dalek::{Signer, SigningKey};
use sha2::{Digest, Sha256};

/// The repository root, from this crate's manifest directory.
fn repo(path: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("persist/ has a parent")
        .join(path)
}

fn read(path: PathBuf) -> Vec<u8> {
    std::fs::read(&path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()))
}

fn parse_hex32(value: &str) -> [u8; 32] {
    assert_eq!(value.len(), 64, "not a hex32: {value}");
    let mut out = [0u8; 32];
    for (index, chunk) in value.as_bytes().chunks_exact(2).enumerate() {
        out[index] = u8::from_str_radix(std::str::from_utf8(chunk).expect("ascii"), 16)
            .expect("lowercase hex");
    }
    out
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn json(bytes: &[u8]) -> serde_json::Value {
    serde_json::from_slice(bytes).expect("artifact is JSON")
}

fn string_at(value: &serde_json::Value, pointer: &str) -> String {
    value
        .pointer(pointer)
        .and_then(serde_json::Value::as_str)
        .unwrap_or_else(|| panic!("missing {pointer}"))
        .to_owned()
}

/// The world a manifest determines: `content_root` is SHA-256 of the exact manifest
/// bytes and the other three coordinates are its own `scope`. Only `activation_digest`
/// is free, and no membership check reads it — at the ceremony the node's world preview
/// supplies it from the POAG1 content-epoch envelope.
fn world_for(manifest: &[u8], activation_digest: [u8; 32]) -> PoaWorldIdentityV2 {
    let scope = json(manifest);
    PoaWorldIdentityV2::new(
        parse_hex32(&string_at(&scope, "/scope/federation_id")),
        Sha256::digest(manifest).into(),
        activation_digest,
        parse_hex32(&string_at(&scope, "/scope/content_session")),
        scope
            .pointer("/scope/content_epoch")
            .and_then(serde_json::Value::as_u64)
            .expect("scope epoch"),
    )
    .expect("world identity")
}

fn signed(
    key: &SigningKey,
    world: PoaWorldIdentityV2,
    counter: u64,
    predecessor: [u8; 32],
) -> SignedPoaWorldActivationEnvelopeV1 {
    let statement = PoaWorldActivationStatementV1::new(
        world,
        counter,
        predecessor,
        PoaWorldActivationKindV1::Advance,
        None,
    )
    .expect("statement");
    let signature = key
        .sign(&statement.signing_message().expect("signing message"))
        .to_bytes();
    SignedPoaWorldActivationEnvelopeV1::new(statement, key.verifying_key().to_bytes(), signature)
        .expect("envelope")
}

/// ⚑ **ARMED GUARD** (2026-08-08) — see `persist/src/poa_world_activation.rs`'s `require_native`.
/// Absent export ⇒ `demand_lean` PANICS naming the capability, rather than returning `false` so
/// each caller can `return` and cargo can print `ok` for a test that asserted nothing.
fn native_available() -> bool {
    dregg_lean_ffi::demand_lean(
        poa_world_activation_available() && poa_activated_content_runtime_available(),
        "the epoch-2 multiplexed PoA world (world-activation + activated-content)",
    )
}

/// Install the pin and the REAL shipped epoch-1 galley world, exactly as the devnet
/// holds it, and return the store plus that activation's envelope digest — the
/// `predecessor_head` any epoch-2 advance must carry.
fn store_at_shipped_epoch_1(key: &SigningKey) -> (PersistentStore, [u8; 32]) {
    let store = PersistentStore::open_in_memory().expect("store");
    store
        .install_poa_world_curator_pin_v1(key.verifying_key().to_bytes())
        .expect("curator pin");

    let manifest = read(repo("poa/artifacts/galley/epoch-1/manifest.json"));
    // The epoch-1 activation digest is whatever the node's preview derived at genesis;
    // nothing in the membership path reads it, so the replay picks a nonzero stand-in.
    let world = world_for(&manifest, [0x51; 32]);
    assert_eq!(world.content_epoch(), 1);
    let installed = store
        .install_poa_world_activation_v1(signed(key, world.clone(), 1, [0; 32]))
        .expect("epoch-1 galley activation installs");
    assert_eq!(
        installed.status(),
        PoaWorldActivationInstallStatusV1::Installed
    );
    store
        .install_poa_activated_content_v1(manifest)
        .expect("epoch-1 galley manifest installs");

    // The "before" state the epoch-2 advance must not break: the galley is served.
    let before = store
        .load_authenticated_poa_galley_policy_v1()
        .expect("the epoch-1 galley policy resolves");
    assert_eq!(before.world(), &world);

    let predecessor = installed
        .active_head()
        .prepared()
        .record()
        .envelope_digest();
    (store, predecessor)
}

/// ⚑ THE DELIVERABLE. One epoch-2 world, one signed activation, one manifest install —
/// and BOTH organs answer.
#[test]
fn both_organs_are_served_from_one_epoch2_activation() {
    if !native_available()
        || !dregg_lean_ffi::demand_lean(
            poa_night_watch_campaign_available(),
            "the PoA night-watch campaign organ",
        )
    {
        return;
    }
    let key = SigningKey::from_bytes(&[0xA2; 32]);
    let (store, predecessor) = store_at_shipped_epoch_1(&key);

    let manifest = read(repo(
        "persist/tests/fixtures/angels-epoch-2-rehearsal/manifest.json",
    ));
    let judge_input = read(repo(
        "persist/tests/fixtures/angels-epoch-2-rehearsal/night-watch-judge-input.json",
    ));

    // The judge input carries the world the night watch will be judged under. The store
    // is activated at exactly that world, so "the galley's world" and "the night
    // watch's world" are one value, not two that agree today.
    let judge_world = json(&judge_input);
    let world = world_for(
        &manifest,
        parse_hex32(&string_at(&judge_world, "/world/activation_digest")),
    );
    assert_eq!(
        hex(&world.content_root()),
        string_at(&judge_world, "/world/content_root"),
        "the judge input names a different manifest root than the manifest hashes to"
    );
    assert_eq!(
        hex(&world.content_session()),
        string_at(&judge_world, "/world/content_session")
    );
    assert_eq!(world.content_epoch(), 2);

    let installed = store
        .install_poa_world_activation_v1(signed(&key, world.clone(), 2, predecessor))
        .expect("the epoch-2 multiplexed world activates off the epoch-1 head");
    assert_eq!(
        installed.status(),
        PoaWorldActivationInstallStatusV1::Installed
    );
    assert_eq!(installed.active_head().counter(), 2);
    assert_eq!(installed.active_head().world(), &world);

    let content = store
        .install_poa_activated_content_v1(manifest.clone())
        .expect("the multiplexed manifest installs under the epoch-2 world");
    assert_eq!(
        content.status(),
        PoaActivatedContentInstallStatusV1::Installed
    );

    // ORGAN 1 — the galley, through the real `dregg_poa_activated_content_authorize`.
    let galley = store
        .load_authenticated_poa_galley_policy_v1()
        .expect("the galley policy resolves from the multiplexed world");
    assert_eq!(galley.world(), &world);
    assert_eq!(galley.manifest_root(), world.content_root());
    let manifest_json = json(&manifest);
    let galley_component = manifest_json["components"]
        .as_array()
        .expect("components")
        .iter()
        .find(|component| component["name"] == "poa.galley-maintenance-daily.policy.v1")
        .expect("the multiplexed manifest carries the galley component");
    assert_eq!(
        hex(&galley.component_sha256()),
        galley_component["sha256"].as_str().expect("sha256")
    );

    // ORGAN 2 — the night watch, through the real
    // `dregg_poa_night_watch_campaign_judge`, over the SAME manifest bytes the store
    // just installed.
    assert_eq!(
        string_at(&judge_world, "/manifest").len(),
        manifest.len(),
        "the judge input embeds different manifest bytes than the store installed"
    );
    let verdict = judge_poa_night_watch_campaign(
        std::str::from_utf8(&judge_input).expect("judge input is UTF-8"),
    )
    .expect("the night-watch judge transport");
    match verdict {
        PoaNightWatchVerdict::Accepted(reply) => {
            assert!(
                reply.contains("POA-NIGHT-WATCH"),
                "unexpected judge reply: {reply}"
            );
        }
        PoaNightWatchVerdict::Refused => {
            panic!("the night watch is not served by the multiplexed world");
        }
    }

    // The single-active-head invariant: `audit_tables_in` refuses `heads.len() > 1`,
    // re-verifies every signature, and re-invokes Lean on every edge.
    store
        .audit_poa_world_activation_v1()
        .expect("the activation lineage audits with exactly one head");
    store
        .audit_poa_activated_content_v1()
        .expect("both content rows audit");
    let head = store
        .load_poa_active_world_v1()
        .expect("head loads")
        .expect("a head exists");
    assert_eq!(head.world(), &world);
    assert_eq!(head.counter(), 2);
}

/// ⚑ The failure the multiplexed world prevents: a night-watch-ONLY epoch-2 world
/// takes the head and the galley cannot be served from it at all.
#[test]
fn the_single_component_epoch2_world_evicts_the_galley() {
    if !native_available() {
        return;
    }
    let key = SigningKey::from_bytes(&[0xA3; 32]);
    let (store, predecessor) = store_at_shipped_epoch_1(&key);

    let manifest = read(repo(
        "persist/tests/fixtures/angels-epoch-2-rehearsal/single-component-manifest.json",
    ));
    assert_eq!(
        json(&manifest)["components"]
            .as_array()
            .expect("components")
            .len(),
        1,
        "this fixture must carry the night-watch component ALONE"
    );
    let world = world_for(&manifest, [0x52; 32]);

    store
        .install_poa_world_activation_v1(signed(&key, world.clone(), 2, predecessor))
        .expect("the single-component epoch-2 world activates and takes the head");

    // The eviction, in two shapes. The manifest itself cannot even be installed: the
    // Lean authority requires the reserved galley component and returns the empty
    // refusal without it.
    assert!(
        store.install_poa_activated_content_v1(manifest).is_err(),
        "a night-watch-only manifest must not install for a world the galley is served from"
    );
    // And with no row for the new world, the galley policy carrier cannot be made —
    // this is the 503.
    assert!(
        store.load_authenticated_poa_galley_policy_v1().is_err(),
        "GALLEY SEALED: the galley must be unreachable once the head moves to a \
         single-component world"
    );
    // The epoch-1 row is still there and still audits; it is history, not authority.
    store
        .audit_poa_activated_content_v1()
        .expect("the epoch-1 content row still audits");
}

/// The SHIPPED epoch-2 bytes — `poa/artifacts/angels-epoch-2/manifest.json`, the ones
/// the ceremony signs — install and serve the galley. The night-watch half of these
/// exact bytes is decided in Lean; see this file's header for why it cannot be judged
/// here.
#[test]
fn the_shipped_multiplexed_manifest_installs_and_serves_the_galley() {
    if !native_available() {
        return;
    }
    let key = SigningKey::from_bytes(&[0xA4; 32]);
    let (store, predecessor) = store_at_shipped_epoch_1(&key);

    let manifest = read(repo("poa/artifacts/angels-epoch-2/manifest.json"));
    let provenance = json(&read(repo("poa/artifacts/angels-epoch-2/world.json")));
    let world = world_for(&manifest, [0x53; 32]);
    assert_eq!(
        hex(&world.content_root()),
        string_at(&provenance, "/content_root"),
        "the emitted provenance names a different content root than the manifest hashes to"
    );
    assert_eq!(world.content_epoch(), 2);

    store
        .install_poa_world_activation_v1(signed(&key, world.clone(), 2, predecessor))
        .expect("the shipped epoch-2 world activates off the epoch-1 head");
    store
        .install_poa_activated_content_v1(manifest.clone())
        .expect("the shipped multiplexed manifest installs");

    let galley = store
        .load_authenticated_poa_galley_policy_v1()
        .expect("the galley policy resolves from the shipped multiplexed world");
    assert_eq!(galley.world(), &world);

    // Both components are present, in the strictly ascending name order
    // `Manifest.validB` requires, and the night-watch one is byte-identical to the
    // separately emitted component file.
    let components = json(&manifest)["components"]
        .as_array()
        .expect("components")
        .clone();
    assert_eq!(components.len(), 2);
    assert_eq!(
        components[0]["name"], "poa.galley-maintenance-daily.policy.v1",
        "the galley component must sort first"
    );
    assert_eq!(components[1]["name"], "poa.night-watch-campaign.config.v1");
    assert_eq!(
        components[1]["bytes_utf8"].as_str().expect("config bytes"),
        std::str::from_utf8(&read(repo(
            "poa/artifacts/angels-epoch-2/night-watch-config.json"
        )))
        .expect("config UTF-8")
    );

    store
        .audit_poa_world_activation_v1()
        .expect("the shipped lineage audits");
    store
        .audit_poa_activated_content_v1()
        .expect("the shipped content row audits");
}

/// The carry, checked against the SHIPPED epoch-1 artifacts rather than described: the
/// galley policy moved exactly `content_epoch`, and the night-watch config moved
/// exactly `progression.content_session` and `progression.content_epoch`.
#[test]
fn the_epoch2_components_are_carried_not_reauthored() {
    let epoch1_galley: serde_json::Value = serde_json::from_str(
        json(&read(repo("poa/artifacts/galley/epoch-1/manifest.json")))["components"][0]
            ["bytes_utf8"]
            .as_str()
            .expect("epoch-1 galley bytes"),
    )
    .expect("galley policy JSON");
    let epoch2_galley = json(&read(repo(
        "poa/artifacts/angels-epoch-2/galley-policy.json",
    )));
    let galley_moved: Vec<&String> = epoch1_galley
        .as_object()
        .expect("object")
        .iter()
        .filter(|(field, value)| epoch2_galley.get(*field) != Some(*value))
        .map(|(field, _)| field)
        .collect();
    assert_eq!(
        galley_moved,
        vec!["content_epoch"],
        "the galley component must move its epoch and nothing else"
    );
    assert_eq!(epoch1_galley["content_epoch"], 1);
    assert_eq!(epoch2_galley["content_epoch"], 2);
    assert_eq!(
        epoch1_galley.as_object().expect("object").len(),
        epoch2_galley.as_object().expect("object").len(),
        "no field was added or dropped"
    );

    let epoch1_config: serde_json::Value = serde_json::from_str(
        json(&read(repo(
            "poa/artifacts/night-watch/epoch-1/manifest.json",
        )))["components"][0]["bytes_utf8"]
            .as_str()
            .expect("epoch-1 config bytes"),
    )
    .expect("config JSON");
    let epoch2_config = json(&read(repo(
        "poa/artifacts/angels-epoch-2/night-watch-config.json",
    )));
    let config_moved: Vec<&String> = epoch1_config
        .as_object()
        .expect("object")
        .iter()
        .filter(|(field, value)| epoch2_config.get(*field) != Some(*value))
        .map(|(field, _)| field)
        .collect();
    assert_eq!(
        config_moved,
        vec!["progression"],
        "only the progression identity may move; roster, rules, log stream and slot \
         commitment are carried"
    );
    let progression_moved: Vec<&String> = epoch1_config["progression"]
        .as_object()
        .expect("object")
        .iter()
        .filter(|(field, value)| epoch2_config["progression"].get(*field) != Some(*value))
        .map(|(field, _)| field)
        .collect();
    assert_eq!(progression_moved, vec!["content_epoch", "content_session"]);
    assert_eq!(
        epoch1_config["slot_commitment"], epoch2_config["slot_commitment"],
        "the slot commitment is CARRIED — HiddenInstance.commit reads (secret, slot) only"
    );
    assert_eq!(epoch1_config["roster"], epoch2_config["roster"]);
    assert_eq!(epoch1_config["rules"], epoch2_config["rules"]);
    assert_eq!(epoch1_config["log_stream"], epoch2_config["log_stream"]);
}
