//! Durable fhEgg operation journal: crash/reopen, restart-stable replay refusal,
//! and fail-closed tamper checks without persisting trader plaintext.

#![cfg(feature = "fhegg-settlement")]

/// The verified settlement gate this binary installs before every test — see
/// `tests/support/mod.rs`. Without it `settle_ring_verified` refuses every award as
/// NEVER JUDGED, which is a host-wiring fact about this binary and not a market verdict.
mod support;

use std::fs;
use std::path::PathBuf;
use std::time::Duration;

use dreggnet_market::fhegg_transport::{
    FHEGG_SETTLEMENT_DISCLOSURE, FHEGG_SETTLEMENT_OPERATION, FheggSettlementBundle,
};
use dreggnet_market::{DarkBazaarOffering, TURN_LIST};
use dreggnet_offerings::{
    Action, BinaryOperationError, DreggIdentity, FileResumeStore, HostOperationError, Offering,
    OfferingHost, Outcome, ResumeError, SessionConfig, SessionId, SessionResumeStore,
};
use ed25519_dalek::SigningKey;
use fhegg_fhe::attestation::{
    AttestedClearingReceipt, AuthenticatedQuorumVerifier, BfvPublicIdentity,
    ComputationIntegrityEvidence, ComputationIntegrityResidual, ExpectedClearingContext,
};
use fhegg_fhe::mpc::Crossing;
use fhegg_fhe::mpc_party::{PartyMpcSession, simulate_public_transcript};
use fhegg_fhe::order_ingress::{
    AuthenticatedOrderBook, OrderEncryptionOpening, OrderIngressSession, SignedOrderSubmission,
};
use fhegg_fhe::threshold::{
    BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, ThresholdParty,
};
use fhegg_fhe::{Order, Side};
use rand::{SeedableRng, rngs::StdRng};

const SEED: u64 = 0xF4_E6_70;

fn actor(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_string())
}

fn scratch_dir() -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "dregg-fhegg-restart-{}-{}",
        std::process::id(),
        SEED
    ));
    let _ = fs::remove_dir_all(&dir);
    dir
}

fn configured_offering(committee: &[SigningKey; 2]) -> DarkBazaarOffering {
    DarkBazaarOffering::with_fhegg_quorum(
        committee
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        2,
    )
    .expect("test verifier")
    .with_fhegg_source_verifier(
        SigningKey::from_bytes(&[0x29; 32])
            .verifying_key()
            .to_bytes(),
    )
    .expect("source verifier")
}

fn land_board(host: &mut OfferingHost, id: &SessionId, bid_actions: &[(Action, DreggIdentity)]) {
    assert!(matches!(
        host.advance(
            DarkBazaarOffering::KEY,
            id,
            Action::new(TURN_LIST, TURN_LIST, 1, true),
            actor("seller"),
        ),
        Some(Outcome::Landed { .. })
    ));
    for (action, who) in bid_actions {
        assert!(matches!(
            host.advance(DarkBazaarOffering::KEY, id, action.clone(), who.clone()),
            Some(Outcome::Landed { .. })
        ));
    }
}

fn collective_key(params: &BfvParams) -> (KeygenSession, CollectivePublicKey) {
    let keygen = KeygenSession::from_seed(2, [0x21; 32]).unwrap();
    let mut coordinator = KeygenCoordinator::new(keygen.clone(), params.clone());
    for party in 0..2 {
        let (state, contribution) = ThresholdParty::join(&keygen, party, params).unwrap();
        coordinator.accept(contribution).unwrap();
        drop(state);
    }
    (keygen, coordinator.finish().unwrap())
}

struct WireFixture {
    wire: Vec<u8>,
    bid_actions: Vec<(Action, DreggIdentity)>,
}

fn wire_for(committee: &[SigningKey; 2]) -> WireFixture {
    // The producer sees a public projection of the exact same deterministic
    // board. No session-internal bid plaintext is copied into the bundle.
    let source_verifier = SigningKey::from_bytes(&[0x29; 32]);
    let offering = DarkBazaarOffering::new()
        .with_fhegg_source_verifier(source_verifier.verifying_key().to_bytes())
        .unwrap();
    let mut market = offering
        .open(SessionConfig::with_seed(SEED))
        .expect("fixture market");
    assert!(
        offering
            .advance(
                &mut market,
                Action::new(TURN_LIST, TURN_LIST, 1, true),
                actor("seller"),
            )
            .landed()
    );
    let params = BfvParams::fold_set();
    let (keygen, collective) = collective_key(&params);
    let ingress = OrderIngressSession::new(
        market.fhegg_order_ingress_nonce().unwrap(),
        4,
        &params,
        &collective,
    )
    .unwrap();
    let trader_keys = [
        SigningKey::from_bytes(&[0x40; 32]),
        SigningKey::from_bytes(&[0x41; 32]),
        SigningKey::from_bytes(&[0x42; 32]),
    ];
    let mut book = AuthenticatedOrderBook::new(
        ingress.clone(),
        trader_keys
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
    )
    .unwrap();
    let mut bid_actions = Vec::new();
    for (trader, (who, side, limit)) in [
        ("seller", Side::Ask, 1usize),
        ("alice", Side::Bid, 2),
        ("bob", Side::Bid, 3),
    ]
    .into_iter()
    .enumerate()
    {
        let order = Order {
            side,
            limit,
            qty: 1,
        };
        let opening = OrderEncryptionOpening::from_seed([0x51 + trader as u8; 32]);
        let (submission, _, _) = SignedOrderSubmission::encrypt_and_sign_with_opening(
            &ingress,
            trader,
            0,
            &order,
            &params,
            &collective,
            &trader_keys[trader],
            opening,
        )
        .unwrap();
        let binding = book
            .accept_opened(submission, &order, opening, &params, &collective)
            .unwrap();
        let action = if matches!(side, Side::Ask) {
            let certificate =
                binding.certify_listing_for_market(who.as_bytes(), [0xA5; 32], &source_verifier);
            DarkBazaarOffering::fhegg_listing_source_action(&certificate)
        } else {
            let certificate = binding.certify_for_market(who.as_bytes(), &source_verifier);
            DarkBazaarOffering::fhegg_source_bound_bid_action(limit as i64, &certificate)
        };
        let identity = actor(who);
        assert!(
            offering
                .advance(&mut market, action.clone(), identity.clone())
                .landed()
        );
        bid_actions.push((action, identity));
    }

    let verifier = AuthenticatedQuorumVerifier::new(
        committee
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        2,
    )
    .unwrap();
    let session = PartyMpcSession::new(
        market.fhegg_settlement_session_nonce().unwrap(),
        2,
        4,
        8,
        params.plaintext_modulus(),
        Duration::from_secs(1),
    )
    .unwrap();
    let bfv = BfvPublicIdentity::from_public(&params, &keygen, &collective);
    let (_, mut inputs) = book.finish().into_parts();
    inputs.push(market.fhegg_source_input().unwrap());
    let crossing = Crossing {
        p_star: Some(3),
        v_star: 1,
    };
    let transcript =
        simulate_public_transcript(&crossing, &session, &mut StdRng::seed_from_u64(SEED)).unwrap();
    let expected = ExpectedClearingContext {
        session: &session,
        ordered_roster: verifier.ordered_roster(),
        bfv: &bfv,
        ordered_inputs: &inputs,
        transcript: &transcript,
        crossing: &crossing,
    };
    let mut receipt = AttestedClearingReceipt::issue(
        &expected,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .unwrap();
    let digest = receipt.claim_digest();
    let signatures = committee
        .iter()
        .enumerate()
        .map(|(index, key)| verifier.sign_claim(&digest, index, key).unwrap())
        .collect::<Vec<_>>();
    receipt.computation_integrity = verifier.assemble_evidence(&digest, &signatures).unwrap();
    WireFixture {
        wire: FheggSettlementBundle::new(&expected, &receipt)
            .unwrap()
            .to_wire_bytes(),
        bid_actions,
    }
}

#[test]
fn settled_operation_survives_restart_burns_replay_and_refuses_journal_tamper() {
    support::install_verified_settlement_gate();
    let committee = [
        SigningKey::from_bytes(&[0x31; 32]),
        SigningKey::from_bytes(&[0x32; 32]),
    ];
    let fixture = wire_for(&committee);
    let wire = fixture.wire;
    let bid_actions = fixture.bid_actions;
    let dir = scratch_dir();
    let store = FileResumeStore::open(&dir).expect("durable store");
    let id = SessionId::new("shielded-market");

    let mut host = OfferingHost::new().with_resume_store(Box::new(store.clone()));
    host.register(
        DarkBazaarOffering::KEY,
        "Dark Bazaar",
        configured_offering(&committee),
    );
    host.open_session(
        DarkBazaarOffering::KEY,
        id.clone(),
        SessionConfig::with_seed(SEED),
    )
    .unwrap();
    land_board(&mut host, &id, &bid_actions);
    let applied = host
        .invoke_binary_operation(
            DarkBazaarOffering::KEY,
            &id,
            FHEGG_SETTLEMENT_OPERATION,
            &wire,
            actor("settlement-worker"),
        )
        .expect("authenticated settlement lands");
    let commitment_before = host.commitment(DarkBazaarOffering::KEY, &id).unwrap();
    let journal = store
        .load(DarkBazaarOffering::KEY, &id)
        .expect("operation persisted");
    assert_eq!(journal.operations.len(), 1);
    let persisted = &journal.operations[0];
    assert_eq!(persisted.name, FHEGG_SETTLEMENT_OPERATION);
    assert_eq!(persisted.actor, actor("settlement-worker"));
    assert_eq!(persisted.payload_digest, *blake3::hash(&wire).as_bytes());
    assert_eq!(persisted.replay_material, wire);
    assert_eq!(persisted.receipt, applied);
    assert_eq!(persisted.replay_disclosure, FHEGG_SETTLEMENT_DISCLOSURE);
    assert!(
        persisted
            .replay_disclosure
            .contains("fhEgg replay sidecar never stores order plaintext")
    );
    assert!(
        !persisted
            .replay_material
            .windows(32)
            .any(|window| window == [0x51; 32]),
        "the exact-encryption randomness opening is never retained"
    );

    drop(host); // process death: only the file journal remains
    let mut reopened = OfferingHost::new().with_resume_store(Box::new(store.clone()));
    reopened.register(
        DarkBazaarOffering::KEY,
        "Dark Bazaar",
        configured_offering(&committee),
    );
    let results = reopened.resume_all();
    assert_eq!(results.len(), 1);
    assert!(
        results[0].1.is_ok(),
        "restart re-verifies the public bundle"
    );
    assert_eq!(
        reopened.commitment(DarkBazaarOffering::KEY, &id).unwrap(),
        commitment_before,
        "opaque settlement mutation is restored exactly"
    );

    // The resume itself consumed the claim in the new process's replay guard.
    // Recreate the same deterministic board under another id: session/source
    // joins pass, then the restored replay floor refuses the claim.
    let replay_probe = SessionId::new("same-board-replay-probe");
    reopened
        .open_session(
            DarkBazaarOffering::KEY,
            replay_probe.clone(),
            SessionConfig::with_seed(SEED),
        )
        .unwrap();
    land_board(&mut reopened, &replay_probe, &bid_actions);
    let replay = reopened
        .invoke_binary_operation(
            DarkBazaarOffering::KEY,
            &replay_probe,
            FHEGG_SETTLEMENT_OPERATION,
            &persisted.replay_material,
            actor("replayer"),
        )
        .expect_err("accepted claim stays burnt after restart");
    assert!(matches!(
        replay,
        HostOperationError::Operation(BinaryOperationError::Refused(reason))
            if reason.contains("ReplayDetected")
    ));

    let mut bad_material = journal.clone();
    bad_material.operations[0].replay_material[0] ^= 1;
    let mut rejecting = OfferingHost::new();
    rejecting.register(
        DarkBazaarOffering::KEY,
        "Dark Bazaar",
        configured_offering(&committee),
    );
    assert!(matches!(
        rejecting.resume(&bad_material),
        Err(ResumeError::OperationRefused { index: 0, .. })
    ));
    assert!(!rejecting.is_open(DarkBazaarOffering::KEY, &id));

    let mut bad_result = journal;
    bad_result.operations[0].receipt.public_fields[0].1 = "999".to_string();
    let mut rejecting = OfferingHost::new();
    rejecting.register(
        DarkBazaarOffering::KEY,
        "Dark Bazaar",
        configured_offering(&committee),
    );
    assert!(matches!(
        rejecting.resume(&bad_result),
        Err(ResumeError::OperationRefused { index: 0, .. })
    ));
    assert!(!rejecting.is_open(DarkBazaarOffering::KEY, &id));

    // Corrupt the actual durable sidecar, then simulate another process boot.
    // The store must keep the session visible and resume must report a refusal;
    // corruption must never look like "no session" and fresh-mint over it.
    drop(reopened);
    let sidecar = fs::read_dir(&dir)
        .unwrap()
        .flatten()
        .map(|entry| entry.path())
        .find(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.contains(".op."))
        })
        .expect("fhEgg replay sidecar");
    fs::write(sidecar, b"corrupt durable evidence").unwrap();
    let mut rejecting = OfferingHost::new().with_resume_store(Box::new(store));
    rejecting.register(
        DarkBazaarOffering::KEY,
        "Dark Bazaar",
        configured_offering(&committee),
    );
    let results = rejecting.resume_all();
    let settled_result = results
        .iter()
        .find(|(log, _)| log.id == id)
        .expect("settled session remains enumerable after sidecar corruption");
    assert!(matches!(
        &settled_result.1,
        Err(ResumeError::OperationRefused { index: 0, .. })
    ));
    assert!(!rejecting.is_open(DarkBazaarOffering::KEY, &id));

    let _ = fs::remove_dir_all(dir);
}
