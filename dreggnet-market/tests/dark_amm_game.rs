//! An external BFV producer drives the hosted encrypted-amount Dark Pool; bad
//! products are atomic refusals and accepted ciphertext requests restart-replay.

#![cfg(feature = "dark-amm-game")]

use dreggnet_market::dark_amm_game::{
    DARK_AMM_DISCLOSURE, DARK_AMM_OFFERING_KEY, DARK_AMM_OPERATION, DarkAmmGameOffering,
    DarkAmmHostKeyMaterial, DarkAmmPublicSession, produce_encrypted_swap,
};
use dreggnet_market::{DARK_BAZAAR_OFFERING_KEY, DarkBazaarOffering, TURN_LIST};
use dreggnet_offerings::resume::{InMemoryResumeStore, SessionResumeStore};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingHost, Outcome, ResumeError, SessionConfig, SessionId,
};
use rand_09::SeedableRng;
use rand_09::rngs::StdRng;
use std::process::Command;

const SEED: u64 = 0xDA12_9000;

fn keys(seed: u64) -> DarkAmmHostKeyMaterial {
    let mut rng = StdRng::seed_from_u64(seed);
    DarkAmmHostKeyMaterial::generate(&mut rng).expect("deployment BFV keys")
}

fn request(public: &DarkAmmPublicSession, dx: u64, dy: u64, rng_seed: u64) -> Vec<u8> {
    let mut rng = StdRng::seed_from_u64(rng_seed);
    produce_encrypted_swap(public, dx, dy, 200, 400, &mut rng)
        .expect("external producer encrypts")
        .to_wire_bytes()
}

#[test]
fn encrypted_swaps_are_atomic_replayable_and_absent_from_the_public_surface() {
    let key_material = keys(0xD4);
    let secret_key_wire = key_material.to_secret_wire_bytes();
    let public = DarkAmmGameOffering::demo(key_material.clone())
        .public_session_for_seed(SEED)
        .expect("public producer context");
    let public_wire = public.to_wire_bytes();
    assert_eq!(
        DarkAmmPublicSession::from_wire_bytes(&public_wire).unwrap(),
        public
    );
    let probe_offering = DarkAmmGameOffering::demo(key_material.clone());
    let probe_session = probe_offering
        .open(SessionConfig::with_seed(SEED))
        .expect("same host config opens");
    assert_eq!(
        probe_session.public_session(),
        public,
        "offline public context must reproduce the opened session"
    );

    let wrong = request(&public, 50, 301, 1);
    let first = request(&public, 50, 300, 2);
    let second = request(&public.clone().at_sequence(1), 150, 300, 3);

    let store = InMemoryResumeStore::new();
    let id = SessionId::new("encrypted-dark-pool");
    let mut host = OfferingHost::new().with_resume_store(Box::new(store.clone()));
    host.register(
        DARK_AMM_OFFERING_KEY,
        "The Dark Bazaar — encrypted pool",
        DarkAmmGameOffering::demo(key_material.clone()),
    );
    host.open_session(
        DARK_AMM_OFFERING_KEY,
        id.clone(),
        SessionConfig::with_seed(SEED),
    )
    .unwrap();

    let descriptor = host
        .binary_operations(DARK_AMM_OFFERING_KEY, &id)
        .unwrap()
        .into_iter()
        .find(|operation| operation.name == DARK_AMM_OPERATION)
        .expect("encrypted swap is discoverable");
    assert_eq!(descriptor.disclosure, DARK_AMM_DISCLOSURE);

    let refused = host
        .invoke_binary_operation(
            DARK_AMM_OFFERING_KEY,
            &id,
            DARK_AMM_OPERATION,
            &wrong,
            DreggIdentity("wrong-quote".to_string()),
        )
        .expect_err("wrong encrypted quote must refuse")
        .to_string();
    assert!(refused.contains("constant-product equality"), "{refused}");
    assert!(
        !refused.contains("90300"),
        "the API must not echo the raw rejected product: {refused}"
    );
    assert_eq!(
        store
            .load(DARK_AMM_OFFERING_KEY, &id)
            .unwrap()
            .operations
            .len(),
        0
    );

    let first_receipt = host
        .invoke_binary_operation(
            DARK_AMM_OFFERING_KEY,
            &id,
            DARK_AMM_OPERATION,
            &first,
            DreggIdentity("veiled-trader-a".to_string()),
        )
        .expect("first exact encrypted quote lands");
    assert_eq!(
        first_receipt
            .public_fields
            .iter()
            .map(|(key, _)| key.as_str())
            .collect::<Vec<_>>(),
        vec!["sequence", "invariant", "requestDigest", "acceptedSwaps"],
        "the public game consequence is an exact allowlist, not a projection of private input"
    );
    assert_eq!(first_receipt.public_fields[0].1, "0");
    assert!(first_receipt.public_fields.iter().all(|(key, _)| {
        !matches!(
            key.as_str(),
            "actor"
                | "dx"
                | "dy"
                | "reserveX"
                | "reserveY"
                | "ciphertext"
                | "witness"
                | "opening"
                | "secretKey"
                | "rejectedProduct"
        )
    }));

    assert!(
        host.invoke_binary_operation(
            DARK_AMM_OFFERING_KEY,
            &id,
            DARK_AMM_OPERATION,
            &first,
            DreggIdentity("replayer".to_string()),
        )
        .is_err(),
        "the sequence cursor refuses replay"
    );
    host.invoke_binary_operation(
        DARK_AMM_OFFERING_KEY,
        &id,
        DARK_AMM_OPERATION,
        &second,
        DreggIdentity("veiled-trader-b".to_string()),
    )
    .expect("second linked exact encrypted quote lands");

    let surface = format!(
        "{:?}",
        host.render(DARK_AMM_OFFERING_KEY, &id).unwrap().view()
    );
    assert!(surface.contains("2 encrypted swap(s) accepted"));
    assert!(surface.contains("public invariant k=90000"));
    assert!(surface.contains("next sequence 2"));
    assert!(surface.contains("Reserve x, reserve y, dx, and dy are absent"));

    let log = store
        .load(DARK_AMM_OFFERING_KEY, &id)
        .expect("durable operation journal");
    assert_eq!(log.operations.len(), 2);
    assert!(
        log.operations
            .iter()
            .all(|operation| operation.replay_is_canonical_request)
    );
    assert!(log.operations.iter().all(|operation| {
        operation.replay_disclosure == DARK_AMM_DISCLOSURE
            && operation.replay_material != public_wire
    }));

    // The public receipt id now binds the routed player under the pool's
    // internal cryptographic session. Substituting only the durable actor must
    // no longer reproduce the accepted receipt during restart.
    let mut bad_actor = log.clone();
    bad_actor.operations[0].actor = DreggIdentity("receipt-thief".to_string());
    let mut rejecting = OfferingHost::new();
    rejecting.register(
        DARK_AMM_OFFERING_KEY,
        "The Dark Bazaar — encrypted pool",
        DarkAmmGameOffering::demo(key_material.clone()),
    );
    assert!(matches!(
        rejecting.resume(&bad_actor),
        Err(ResumeError::OperationRefused { index: 0, .. })
    ));
    assert!(!rejecting.is_open(DARK_AMM_OFFERING_KEY, &id));

    let mut bad_receipt = log.clone();
    bad_receipt.operations[0].receipt.receipt_id[0] ^= 1;
    let mut rejecting = OfferingHost::new();
    rejecting.register(
        DARK_AMM_OFFERING_KEY,
        "The Dark Bazaar — encrypted pool",
        DarkAmmGameOffering::demo(key_material.clone()),
    );
    assert!(matches!(
        rejecting.resume(&bad_receipt),
        Err(ResumeError::OperationRefused { index: 0, .. })
    ));
    assert!(!rejecting.is_open(DARK_AMM_OFFERING_KEY, &id));

    let mut bad_public_consequence = log.clone();
    bad_public_consequence.operations[0].receipt.public_fields[0].1 = "999".to_string();
    let mut rejecting = OfferingHost::new();
    rejecting.register(
        DARK_AMM_OFFERING_KEY,
        "The Dark Bazaar — encrypted pool",
        DarkAmmGameOffering::demo(key_material.clone()),
    );
    assert!(matches!(
        rejecting.resume(&bad_public_consequence),
        Err(ResumeError::OperationRefused { index: 0, .. })
    ));
    assert!(!rejecting.is_open(DARK_AMM_OFFERING_KEY, &id));
    drop(host);

    // A new process with the same secret host configuration reconstructs the
    // per-session BFV key/pool and re-runs both opaque requests in order.
    let mut reopened = OfferingHost::new().with_resume_store(Box::new(store));
    reopened.register(
        DARK_AMM_OFFERING_KEY,
        "The Dark Bazaar — encrypted pool",
        DarkAmmGameOffering::demo(
            DarkAmmHostKeyMaterial::from_secret_wire_bytes(&secret_key_wire)
                .expect("protected deployment key reload"),
        ),
    );
    let resumed = reopened.resume_all();
    assert_eq!(resumed.len(), 1);
    assert!(resumed[0].1.is_ok(), "{resumed:?}");
    let surface = format!(
        "{:?}",
        reopened.render(DARK_AMM_OFFERING_KEY, &id).unwrap().view()
    );
    assert!(surface.contains("2 encrypted swap(s) accepted"));
}

#[test]
fn crawl_and_encrypted_game_share_a_session_token_without_sharing_rules_or_state() {
    assert_eq!(DARK_BAZAAR_OFFERING_KEY, "bazaar");
    assert_eq!(DARK_AMM_OFFERING_KEY, "dark-pool");
    assert_ne!(DARK_BAZAAR_OFFERING_KEY, DARK_AMM_OFFERING_KEY);

    let key_material = keys(0xD6);
    let pool_public = DarkAmmGameOffering::demo(key_material.clone())
        .public_session_for_seed(SEED)
        .expect("public producer context");
    let private_request = request(&pool_public, 50, 300, 0xD601);
    let same_token = SessionId::new("one-player-slot");
    let store = InMemoryResumeStore::new();
    let mut host = OfferingHost::new().with_resume_store(Box::new(store.clone()));
    host.register(
        DARK_BAZAAR_OFFERING_KEY,
        "Dark Bazaar crawl",
        DarkBazaarOffering::new(),
    );
    host.register(
        DARK_AMM_OFFERING_KEY,
        "Dark Bazaar encrypted pool",
        DarkAmmGameOffering::demo(key_material),
    );
    for offering in [DARK_BAZAAR_OFFERING_KEY, DARK_AMM_OFFERING_KEY] {
        host.open_session(offering, same_token.clone(), SessionConfig::with_seed(SEED))
            .unwrap();
    }

    let crawl_operations = host
        .binary_operations(DARK_BAZAAR_OFFERING_KEY, &same_token)
        .unwrap();
    assert!(crawl_operations.is_empty());
    let private_operations = host
        .binary_operations(DARK_AMM_OFFERING_KEY, &same_token)
        .unwrap();
    assert_eq!(private_operations.len(), 1);
    assert_eq!(private_operations[0].name, DARK_AMM_OPERATION);

    // A private-game upload addressed to the public crawl is not reinterpreted
    // as a bid or settlement and records no operation.
    assert!(
        host.invoke_binary_operation(
            DARK_BAZAAR_OFFERING_KEY,
            &same_token,
            DARK_AMM_OPERATION,
            &private_request,
            DreggIdentity("cross-route-attacker".to_string()),
        )
        .is_err()
    );
    assert_eq!(
        store
            .load(DARK_BAZAAR_OFFERING_KEY, &same_token)
            .unwrap()
            .operations
            .len(),
        0
    );

    // Conversely, the crawl's ordinary LIST action reaches the encrypted game
    // only as a real refusal. It cannot mutate the pool's sequence or journal.
    let crossed = host
        .advance(
            DARK_AMM_OFFERING_KEY,
            &same_token,
            Action::new(TURN_LIST, TURN_LIST, 1, true),
            DreggIdentity("seller".to_string()),
        )
        .expect("the encrypted session exists");
    assert!(matches!(crossed, Outcome::Refused(_)));
    assert_eq!(
        store
            .load(DARK_AMM_OFFERING_KEY, &same_token)
            .unwrap()
            .operations
            .len(),
        0
    );

    let receipt = host
        .invoke_binary_operation(
            DARK_AMM_OFFERING_KEY,
            &same_token,
            DARK_AMM_OPERATION,
            &private_request,
            DreggIdentity("veiled-player".to_string()),
        )
        .expect("the exact encrypted-game route accepts its request");
    assert_eq!(receipt.operation, DARK_AMM_OPERATION);
    assert_eq!(
        store
            .load(DARK_AMM_OFFERING_KEY, &same_token)
            .unwrap()
            .operations
            .len(),
        1
    );
    assert_eq!(
        store
            .load(DARK_BAZAAR_OFFERING_KEY, &same_token)
            .unwrap()
            .operations
            .len(),
        0,
        "the public crawl remains a distinct session despite the shared frontend token"
    );
}

#[test]
fn direct_session_reverifies_the_encrypted_request_chain() {
    let offering = DarkAmmGameOffering::demo(keys(0xD5));
    let mut session = offering.open(SessionConfig::with_seed(SEED)).unwrap();
    let public = session.public_session();
    let first = request(&public, 50, 300, 9);
    offering
        .invoke_binary_operation(
            &mut session,
            DARK_AMM_OPERATION,
            &first,
            DreggIdentity("private-trader".to_string()),
        )
        .unwrap();
    assert_eq!(session.accepted_swaps(), 1);
    let verified = offering.verify(&session);
    assert!(verified.verified, "{}", verified.detail);
    assert_eq!(verified.turns, 1);
    assert!(verified.detail.contains("canonical ciphertext requests"));
    assert!(verified.detail.contains("single-key boundary"));
}

#[test]
fn offline_tool_keygen_public_export_and_swap_file_drive_the_host() {
    const WEB_SESSION_ID: &str = "dark-pool-cli-e2e";
    let dir = std::env::temp_dir().join(format!(
        "dregg-dark-amm-tool-{}-{}",
        std::process::id(),
        SEED
    ));
    std::fs::create_dir(&dir).expect("unique scratch directory");
    let key_file = dir.join("host.dbak");
    let public_file = dir.join("session.dbap");
    let request_file = dir.join("swap.dbam");
    let second_public_file = dir.join("session-1.dbap");
    let second_request_file = dir.join("swap-1.dbam");
    let tool = env!("CARGO_BIN_EXE_dark-amm-tool");

    let status = Command::new(tool)
        .args(["keygen"])
        .arg(&key_file)
        .status()
        .expect("run keygen");
    assert!(status.success());
    let status = Command::new(tool)
        .args(["public-id"])
        .arg(&key_file)
        .arg(WEB_SESSION_ID)
        .arg(&public_file)
        .status()
        .expect("run public export");
    assert!(status.success());
    let status = Command::new(tool)
        .args(["swap"])
        .arg(&public_file)
        .args(["50", "300", "200", "400"])
        .arg(&request_file)
        .status()
        .expect("run external swap producer");
    assert!(status.success());

    let mut key_bytes = std::fs::read(&key_file).expect("operator key file");
    let keys = DarkAmmHostKeyMaterial::from_secret_wire_bytes(&key_bytes)
        .expect("host reloads protected key");
    key_bytes.fill(0);
    let offering = DarkAmmGameOffering::demo(keys);
    let digest = blake3::hash(WEB_SESSION_ID.as_bytes());
    let web_seed = u64::from_le_bytes(digest.as_bytes()[..8].try_into().unwrap());
    let mut session = offering.open(SessionConfig::with_seed(web_seed)).unwrap();
    offering
        .invoke_binary_operation(
            &mut session,
            DARK_AMM_OPERATION,
            &std::fs::read(&request_file).expect("opaque request file"),
            DreggIdentity("offline-player".to_string()),
        )
        .expect("offline-produced request lands");
    let status = Command::new(tool)
        .args(["cursor"])
        .arg(&public_file)
        .arg("1")
        .arg(&second_public_file)
        .status()
        .expect("advance the public anti-replay cursor");
    assert!(status.success());
    let status = Command::new(tool)
        .args(["swap"])
        .arg(&second_public_file)
        .args(["150", "300", "200", "400"])
        .arg(&second_request_file)
        .status()
        .expect("run second external swap producer");
    assert!(status.success());
    offering
        .invoke_binary_operation(
            &mut session,
            DARK_AMM_OPERATION,
            &std::fs::read(&second_request_file).expect("second opaque request file"),
            DreggIdentity("offline-player-2".to_string()),
        )
        .expect("cursor-advanced offline request lands");
    assert_eq!(session.accepted_swaps(), 2);
    assert!(offering.verify(&session).verified);

    std::fs::remove_dir_all(&dir).expect("remove isolated scratch directory");
}
