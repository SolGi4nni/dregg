//! Remote-host wire boundary for authenticated fhEgg Dark Bazaar settlement.

#![cfg(feature = "fhegg-settlement")]

use std::time::Duration;

use dreggnet_market::fhegg_settlement::FheggSettlementError;
use dreggnet_market::fhegg_transport::{
    FHEGG_SETTLEMENT_DISCLOSURE, FHEGG_SETTLEMENT_OPERATION, FheggSettlementBundle,
    FheggSettlementOperation, FheggTransportError,
};
use dreggnet_market::{DarkBazaarOffering, DarkBazaarSession, TURN_LIST};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};
use ed25519_dalek::SigningKey;
use fhegg_fhe::attestation::{
    AttestationError, AttestedClearingReceipt, AuthenticatedQuorumVerifier, BfvPublicIdentity,
    ComputationIntegrityEvidence, ComputationIntegrityResidual, ExpectedClearingContext,
    InMemoryReplayGuard, InputDigest,
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
use starbridge_sealed_auction::Phase;

const MARKET_SEED: u64 = 0xF4_E6_70;

fn actor(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_string())
}

fn land(
    offering: &DarkBazaarOffering,
    session: &mut DarkBazaarSession,
    turn: &str,
    value: i64,
    who: &str,
) {
    let outcome = offering.advance(session, Action::new(turn, turn, value, true), actor(who));
    assert!(matches!(outcome, Outcome::Landed { .. }));
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

fn live_market(
    offering: &DarkBazaarOffering,
    source_verifier: &SigningKey,
) -> (DarkBazaarSession, Vec<InputDigest>, BfvPublicIdentity) {
    let mut session = offering
        .open(SessionConfig::with_seed(MARKET_SEED))
        .expect("market opens");
    land(offering, &mut session, TURN_LIST, 1, "seller");
    let params = BfvParams::fold_set();
    let (keygen, collective) = collective_key(&params);
    let ingress = OrderIngressSession::new(
        session.fhegg_order_ingress_nonce().unwrap(),
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
                binding.certify_listing_for_market(who.as_bytes(), [0xA5; 32], source_verifier);
            DarkBazaarOffering::fhegg_listing_source_action(&certificate)
        } else {
            let certificate = binding.certify_for_market(who.as_bytes(), source_verifier);
            DarkBazaarOffering::fhegg_source_bound_bid_action(limit as i64, &certificate)
        };
        assert!(offering.advance(&mut session, action, actor(who)).landed());
    }
    let (_, mut inputs) = book.finish().into_parts();
    inputs.push(session.fhegg_source_input().unwrap());
    let bfv = BfvPublicIdentity::from_public(&params, &keygen, &collective);
    (session, inputs, bfv)
}

fn assert_unmutated(session: &DarkBazaarSession, receipts: usize) {
    assert_eq!(session.market().receipts_len(), receipts);
    assert_eq!(session.market().phase(), Some(Phase::Commit));
    assert_eq!(session.market().onledger_phase(), Some(0));
    assert!(!session.is_settled());
}

fn find_unique(bytes: &[u8], needle: &[u8]) -> usize {
    let hits = bytes
        .windows(needle.len())
        .enumerate()
        .filter_map(|(offset, window)| (window == needle).then_some(offset))
        .collect::<Vec<_>>();
    assert_eq!(hits.len(), 1, "test fixture expects one source occurrence");
    hits[0]
}

#[test]
fn owning_bundle_roundtrips_and_frontend_neutral_operation_fails_closed() {
    let source_verifier = SigningKey::from_bytes(&[0x29; 32]);
    let offering = DarkBazaarOffering::new()
        .with_fhegg_source_verifier(source_verifier.verifying_key().to_bytes())
        .unwrap();
    let (mut market, inputs, bfv) = live_market(&offering, &source_verifier);
    let receipts_before = market.market().receipts_len();
    let source_commitment = market.fhegg_source_commitment().expect("live sealed board");
    let nonce = market
        .fhegg_settlement_session_nonce()
        .expect("board-bound session");

    let session = PartyMpcSession::new(
        nonce,
        2,
        4,
        8,
        bfv.plaintext_modulus,
        Duration::from_secs(1),
    )
    .expect("public MPC session");
    let committee_keys = [
        SigningKey::from_bytes(&[0x31; 32]),
        SigningKey::from_bytes(&[0x32; 32]),
    ];
    let verifier = AuthenticatedQuorumVerifier::new(
        committee_keys
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        2,
    )
    .expect("unanimous verifier");
    let crossing = Crossing {
        p_star: Some(3),
        v_star: 1,
    };
    let mut transcript_rng = StdRng::seed_from_u64(0xF4_E6_70);
    let transcript = simulate_public_transcript(&crossing, &session, &mut transcript_rng)
        .expect("strict reveal-only public transcript");
    let expected = ExpectedClearingContext {
        session: &session,
        ordered_roster: verifier.ordered_roster(),
        bfv: &bfv,
        ordered_inputs: &inputs,
        transcript: &transcript,
        crossing: &crossing,
    };

    let mut attestation = AttestedClearingReceipt::issue(
        &expected,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .expect("canonical claim");
    let claim_digest = attestation.claim_digest();
    let signatures = committee_keys
        .iter()
        .enumerate()
        .map(|(party, key)| {
            verifier
                .sign_claim(&claim_digest, party, key)
                .expect("committee signature")
        })
        .collect::<Vec<_>>();
    attestation.computation_integrity = verifier
        .assemble_evidence(&claim_digest, &signatures)
        .expect("unanimous evidence");

    let bundle = FheggSettlementBundle::new(&expected, &attestation).expect("owning bundle");
    let wire = bundle.to_wire_bytes();
    let decoded = FheggSettlementBundle::from_wire_bytes(&wire).expect("strict roundtrip");
    assert_eq!(decoded.to_wire_bytes(), wire, "wire encoding is canonical");
    assert_eq!(decoded.claim_digest(), claim_digest);
    assert_eq!(
        decoded.expected_context().session.quorum_timeout(),
        Duration::from_secs(1),
        "restart wire preserves the exact session domain rather than substituting a verifier timeout",
    );
    assert_eq!(decoded.crossing(), &crossing);
    assert_eq!(decoded.source_inputs(), inputs);
    assert_eq!(FheggSettlementOperation::NAME, FHEGG_SETTLEMENT_OPERATION);
    assert_eq!(
        FheggSettlementOperation::from_bundle(decoded).disclosure(),
        FHEGG_SETTLEMENT_DISCLOSURE
    );

    // Transport parsing is strict and allocation-bounded.
    let mut wrong_magic = wire.clone();
    wrong_magic[0] ^= 1;
    assert!(matches!(
        FheggSettlementBundle::from_wire_bytes(&wrong_magic),
        Err(FheggTransportError::Malformed(_))
    ));
    let mut legacy_v1 = wire.clone();
    legacy_v1[..8].copy_from_slice(b"FHDBv001");
    assert!(matches!(
        FheggSettlementBundle::from_wire_bytes(&legacy_v1),
        Err(FheggTransportError::Malformed(_))
    ));
    let mut invalid_timeout = wire.clone();
    invalid_timeout[80..84].copy_from_slice(&1_000_000_000u32.to_be_bytes());
    assert!(matches!(
        FheggSettlementBundle::from_wire_bytes(&invalid_timeout),
        Err(FheggTransportError::Malformed(_))
    ));
    let mut invalid_preprocessing_tag = wire.clone();
    invalid_preprocessing_tag[84] = 2;
    assert!(matches!(
        FheggSettlementBundle::from_wire_bytes(&invalid_preprocessing_tag),
        Err(FheggTransportError::Malformed(_))
    ));
    assert!(matches!(
        FheggSettlementBundle::from_wire_bytes(&wire[..wire.len() - 1]),
        Err(FheggTransportError::Malformed(_))
    ));
    let mut trailing = wire.clone();
    trailing.push(0);
    assert_eq!(
        FheggSettlementBundle::from_wire_bytes(&trailing).expect_err("no trailing bytes"),
        FheggTransportError::TrailingBytes
    );

    let mut replay_guard = InMemoryReplayGuard::default();

    // Replacing the exact co-endorsed live-board input remains structurally
    // decodable, but the operation refuses it before evidence/replay/mutation.
    let mut wrong_source = wire.clone();
    let source_offset = find_unique(&wrong_source, &source_commitment);
    wrong_source[source_offset] ^= 1;
    let wrong_source_op =
        FheggSettlementOperation::from_wire_bytes(&wrong_source).expect("canonical changed claim");
    assert!(matches!(
        wrong_source_op.execute(&offering, &mut market, &verifier, &mut replay_guard,),
        Err(FheggSettlementError::SourceCommitmentCount { found: 0 })
    ));
    assert_unmutated(&market, receipts_before);

    // Evidence bytes are transportable but not trusted: changing one parses,
    // then the relying-party-selected verifier rejects the exact claim.
    let mut wrong_evidence = wire.clone();
    *wrong_evidence.last_mut().expect("nonempty evidence") ^= 1;
    let wrong_evidence_op = FheggSettlementOperation::from_wire_bytes(&wrong_evidence)
        .expect("tampered evidence is still a framed byte string");
    assert!(matches!(
        wrong_evidence_op.execute(&offering, &mut market, &verifier, &mut replay_guard,),
        Err(FheggSettlementError::Attestation(
            AttestationError::InvalidComputationIntegrityEvidence
        ))
    ));
    assert_unmutated(&market, receipts_before);

    // A binding-only operation is valid transport, never valid settlement.
    let binding_only_receipt = AttestedClearingReceipt::issue(
        &expected,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .expect("binding-only envelope");
    let binding_only_wire = FheggSettlementBundle::new(&expected, &binding_only_receipt)
        .expect("binding-only transport remains explicit")
        .to_wire_bytes();
    let binding_only_op = FheggSettlementOperation::from_wire_bytes(&binding_only_wire)
        .expect("binding-only roundtrip");
    assert!(matches!(
        binding_only_op.execute(&offering, &mut market, &verifier, &mut replay_guard,),
        Err(FheggSettlementError::Attestation(
            AttestationError::ComputationIntegrityResidual(
                ComputationIntegrityResidual::OutputOnlySelfAssertion
            )
        ))
    ));
    assert_unmutated(&market, receipts_before);

    // The valid owning operation reaches and settles the real executor session.
    let operation = FheggSettlementOperation::from_wire_bytes(&wire).expect("host accepts bundle");
    let settled = operation
        .execute(&offering, &mut market, &verifier, &mut replay_guard)
        .expect("fully verified remote result settles");
    assert_eq!(settled.claim_digest, claim_digest);
    assert_eq!((settled.price, settled.volume), (3, 1));
    assert_eq!(settled.winner, actor("bob"));
    assert!(market.is_settled());
    assert!(market.clearing().expect("real clear").conserved());
}
