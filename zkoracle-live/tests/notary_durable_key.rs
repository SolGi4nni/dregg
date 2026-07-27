//! **Durable notary trust root — DRIVEN, no network.** The Phase-E notary key used to be
//! freshly generated per run (a new pin every time, nothing an independent verifier could pin
//! durably). This test persists the key to a file and runs the SEPARATE hosted notary party
//! TWICE from that file, asserting it presents the SAME verifying key both times — the durable
//! trust root a verifier pins out-of-band. It is hermetic (a real localhost socket, no live
//! Bedrock), so it runs by default.

#![cfg(feature = "tlsn-live")]

use std::time::{SystemTime, UNIX_EPOCH};

use dregg_zkoracle_prove::notary_server::{
    generate_notary_key, load_notary_key, load_or_generate_notary_key, save_notary_key,
    spawn_hosted_notary, verifying_key_of,
};

/// A unique temp directory for this test's persisted key (cleaned up at the end).
fn unique_dir() -> std::path::PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let mut p = std::env::temp_dir();
    p.push(format!(
        "zkoracle-notary-durable-{}-{}",
        std::process::id(),
        nanos
    ));
    p
}

/// Spawn the hosted notary from `key`, returning the verifying key it presents in its pin.
/// (No prover connects; we only read the pin, then drop the notary — the task is reclaimed
/// with the current-thread runtime.)
fn pin_key_of(rt: &tokio::runtime::Runtime, key: k256::ecdsa::SigningKey) -> Vec<u8> {
    rt.block_on(async move {
        let notary = spawn_hosted_notary(key, 1)
            .await
            .expect("spawn hosted notary");
        notary.pin().verifying_key.data.clone()
    })
}

#[test]
fn notary_key_is_durable_across_runs() {
    let dir = unique_dir();
    let key_path = dir.join("notary.key");

    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap();

    // FIRST run: no key file yet → provision + persist.
    assert!(!key_path.exists(), "precondition: no key file yet");
    let k1 = load_or_generate_notary_key(&key_path).expect("provision durable key");
    assert!(
        key_path.exists(),
        "the durable key must be persisted to disk on first use"
    );
    let vk1 = pin_key_of(&rt, k1);

    // SECOND run: the key file exists → LOAD it (config mode, not freshly generated).
    let k2 = load_or_generate_notary_key(&key_path).expect("load durable key");
    let vk2 = pin_key_of(&rt, k2);

    // DURABLE: the hosted notary presented the SAME verifying key both runs.
    assert_eq!(
        vk1, vk2,
        "a persisted notary key must yield the SAME verifying key across runs — the durable pin"
    );

    // NON-VACUOUS: an independently generated key differs (so equality above is meaningful).
    let vk_independent = verifying_key_of(&generate_notary_key().unwrap())
        .unwrap()
        .data;
    assert_ne!(
        vk1, vk_independent,
        "an independent fresh key must differ from the durable pin (equality is not trivial)"
    );

    // The bytes loaded from disk reconstruct exactly the persisted key.
    let loaded = load_notary_key(&key_path).expect("reload durable key");
    assert_eq!(
        verifying_key_of(&loaded).unwrap().data,
        vk1,
        "reloading the persisted key yields the pinned verifying key"
    );

    // Explicit save/load round-trips through the hex codec, too.
    let round_path = dir.join("explicit.key");
    let fresh = generate_notary_key().unwrap();
    save_notary_key(&fresh, &round_path).expect("save");
    let reread = load_notary_key(&round_path).expect("reload");
    assert_eq!(
        fresh.to_bytes().as_slice(),
        reread.to_bytes().as_slice(),
        "save→load must be identity on the signing scalar"
    );

    let _ = std::fs::remove_dir_all(&dir);
}
