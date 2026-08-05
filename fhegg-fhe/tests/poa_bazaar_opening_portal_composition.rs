#![cfg(feature = "amm-input-binding")]

// Compile the additive market boundary against fhegg-fhe's own dependency
// cone. This keeps the crypto composition executable even when an unrelated
// dreggnet-market dependency is red before its integration target is reached.
#[rustfmt::skip]
#[allow(dead_code)]
#[path = "../../dreggnet-market/src/poa_bazaar_opening_portal.rs"]
mod portal;

use dregg_circuit_prove::dark_bazaar_private::PrivateOrder;
use ed25519_dalek::SigningKey;
use fhegg_fhe::order_ingress::{
    AuthenticatedOrderBook, OrderIngressSession, SignedOrderSubmission,
};
use fhegg_fhe::threshold::{BfvParams, KeygenCoordinator, KeygenSession, ThresholdParty};
use portal::{
    BazaarExchangeOpeningCertificateV1, BazaarOpeningCertificateV1, BazaarOpeningError,
    ExactBatchKeyV1, ExactBookBindingV1, ExactEnvelopeStatementV1, ExactOrdinaryUnitKeyV1,
    OpeningOrderV1, OpeningSideV1,
};

fn fixture() -> (
    SigningKey,
    ExactEnvelopeStatementV1,
    OpeningOrderV1,
    fhegg_fhe::order_ingress::OrderSourceCertificate,
) {
    let params = BfvParams::fold_set();
    let keygen = KeygenSession::from_seed(1, [0x21; 32]).unwrap();
    let (party, contribution) = ThresholdParty::join(&keygen, 0, &params).unwrap();
    let mut coordinator = KeygenCoordinator::new(keygen, params.clone());
    coordinator.accept(contribution).unwrap();
    drop(party);
    let collective = coordinator.finish().unwrap();

    let ingress = OrderIngressSession::new([0x31; 32], 4, &params, &collective).unwrap();
    let actor = [0x41; 32];
    let trader_key = SigningKey::from_bytes(&[0x51; 32]);
    let source_verifier = SigningKey::from_bytes(&[0x61; 32]);
    let private_order = PrivateOrder::bid(1, 3);
    let encryption_seed = [0x71; 32];
    let submission = SignedOrderSubmission::encrypt_and_sign_private_book_row(
        &ingress,
        0,
        7,
        private_order,
        encryption_seed,
        &params,
        &collective,
        &trader_key,
    )
    .unwrap();
    let mut book =
        AuthenticatedOrderBook::new(ingress, vec![trader_key.verifying_key().to_bytes()]).unwrap();
    let binding = book
        .accept_private_book_opened(
            submission,
            private_order,
            encryption_seed,
            &params,
            &collective,
        )
        .unwrap();
    let source = binding.certify_for_market(&actor, &source_verifier);
    let statement = ExactEnvelopeStatementV1::new(
        actor,
        19,
        [0x81; 32],
        [0x82; 32],
        3,
        22,
        [0x83; 32],
        [0x84; 32],
        source.ciphertext_digest(),
        source.message_digest(),
    );
    let order = OpeningOrderV1::new(0, OpeningSideV1::Bid, 1, 3).unwrap();
    (source_verifier, statement, order, source)
}

#[test]
fn actual_bfv_opening_composes_into_the_exact_poa_statement() {
    let (source_verifier, statement, order, source) = fixture();
    let certificate =
        BazaarOpeningCertificateV1::issue(statement.clone(), order, source, &source_verifier)
            .unwrap();
    let decoded =
        BazaarOpeningCertificateV1::from_wire_bytes(&certificate.to_wire_bytes()).unwrap();
    let verified = decoded.verify(&source_verifier.verifying_key()).unwrap();
    assert_eq!(verified.statement(), &statement);
    assert_eq!(verified.order(), order);

    // All coordinates not present in the nested fhEgg source certificate are
    // covered by the outer source-verifier signature.
    let wire = certificate.to_wire_bytes();
    for offset in [12 + 42, 12 + 122, 12 + 162] {
        let mut substituted = wire.clone();
        substituted[offset] ^= 1;
        let decoded = BazaarOpeningCertificateV1::from_wire_bytes(&substituted).unwrap();
        assert!(matches!(
            decoded.verify(&source_verifier.verifying_key()),
            Err(BazaarOpeningError::InvalidPortalSignature)
        ));
    }
}

#[test]
fn actual_source_certificate_refuses_game_facing_substitutions() {
    let (source_verifier, statement, order, source) = fixture();
    let wrong_actor = ExactEnvelopeStatementV1::new(
        [0x99; 32],
        statement.round(),
        statement.federation_id(),
        statement.content_session(),
        statement.content_epoch(),
        statement.batch_id(),
        statement.source_root(),
        statement.nullifier(),
        statement.ciphertext_commitment(),
        statement.signature_commitment(),
    );
    assert_eq!(
        BazaarOpeningCertificateV1::issue(wrong_actor, order, source.clone(), &source_verifier,),
        Err(BazaarOpeningError::ActorMismatch)
    );
    assert_eq!(
        BazaarOpeningCertificateV1::issue(
            statement.clone(),
            OpeningOrderV1::new(1, OpeningSideV1::Bid, 1, 3).unwrap(),
            source.clone(),
            &source_verifier,
        ),
        Err(BazaarOpeningError::SlotMismatch)
    );
    assert_eq!(
        BazaarOpeningCertificateV1::issue(
            statement.clone(),
            OpeningOrderV1::new(0, OpeningSideV1::Bid, 2, 3).unwrap(),
            source.clone(),
            &source_verifier,
        ),
        Err(BazaarOpeningError::OrderMismatch)
    );
    assert_eq!(
        BazaarOpeningCertificateV1::issue(
            statement.clone(),
            OpeningOrderV1::new(0, OpeningSideV1::Ask, 1, 3).unwrap(),
            source.clone(),
            &source_verifier,
        ),
        Err(BazaarOpeningError::OrderMismatch)
    );
    assert_eq!(
        BazaarOpeningCertificateV1::issue(
            statement.clone(),
            OpeningOrderV1::new(0, OpeningSideV1::Bid, 1, 2).unwrap(),
            source.clone(),
            &source_verifier,
        ),
        Err(BazaarOpeningError::OrderMismatch)
    );

    let wrong_commitment = ExactEnvelopeStatementV1::new(
        statement.actor(),
        statement.round(),
        statement.federation_id(),
        statement.content_session(),
        statement.content_epoch(),
        statement.batch_id(),
        statement.source_root(),
        statement.nullifier(),
        [0xa1; 32],
        statement.signature_commitment(),
    );
    assert_eq!(
        BazaarOpeningCertificateV1::issue(
            wrong_commitment,
            order,
            source.clone(),
            &source_verifier,
        ),
        Err(BazaarOpeningError::CiphertextCommitmentMismatch)
    );

    let wrong_signature = ExactEnvelopeStatementV1::new(
        statement.actor(),
        statement.round(),
        statement.federation_id(),
        statement.content_session(),
        statement.content_epoch(),
        statement.batch_id(),
        statement.source_root(),
        statement.nullifier(),
        statement.ciphertext_commitment(),
        [0xa2; 32],
    );
    assert_eq!(
        BazaarOpeningCertificateV1::issue(wrong_signature, order, source, &source_verifier,),
        Err(BazaarOpeningError::SignatureCommitmentMismatch)
    );
}

#[test]
fn portal_wire_and_configured_key_fail_closed() {
    let (source_verifier, statement, order, source) = fixture();
    let certificate =
        BazaarOpeningCertificateV1::issue(statement.clone(), order, source, &source_verifier)
            .unwrap();
    let wire = certificate.to_wire_bytes();

    let wrong_key = SigningKey::from_bytes(&[0xb1; 32]);
    assert!(certificate.verify(&wrong_key.verifying_key()).is_err());

    let mut wrong_version = wire.clone();
    wrong_version[9] = 2;
    assert_eq!(
        BazaarOpeningCertificateV1::from_wire_bytes(&wrong_version),
        Err(BazaarOpeningError::UnsupportedVersion)
    );
    let mut wrong_side = wire.clone();
    wrong_side[12 + 258 + 1] = 9;
    assert!(matches!(
        BazaarOpeningCertificateV1::from_wire_bytes(&wrong_side),
        Err(BazaarOpeningError::MalformedWire("order side"))
    ));
    let mut changed_source_certificate = wire.clone();
    // Header + statement + order + source-length + source magic/session nonce.
    changed_source_certificate[12 + 258 + 4 + 2 + 8] ^= 1;
    let decoded = BazaarOpeningCertificateV1::from_wire_bytes(&changed_source_certificate).unwrap();
    assert!(matches!(
        decoded.verify(&source_verifier.verifying_key()),
        Err(BazaarOpeningError::InvalidSourceCertificate)
    ));
    assert!(BazaarOpeningCertificateV1::from_wire_bytes(&wire[..wire.len() - 1]).is_err());
    let mut trailing = wire;
    trailing.push(0);
    assert!(matches!(
        BazaarOpeningCertificateV1::from_wire_bytes(&trailing),
        Err(BazaarOpeningError::MalformedWire("trailing bytes"))
    ));

    assert_eq!(
        ExactEnvelopeStatementV1::from_wire_bytes(&statement.to_wire_bytes()).unwrap(),
        statement
    );
    assert!(OpeningOrderV1::new(4, OpeningSideV1::Bid, 1, 3).is_err());
    assert!(OpeningOrderV1::new(0, OpeningSideV1::Bid, 0, 3).is_err());
    assert!(OpeningOrderV1::new(0, OpeningSideV1::Bid, 16, 3).is_err());
    assert!(OpeningOrderV1::new(0, OpeningSideV1::Bid, 1, 4).is_err());
}

#[test]
fn four_real_bfv_openings_bind_one_ordinary_exchange_without_a_privacy_upgrade() {
    let params = BfvParams::fold_set();
    let keygen = KeygenSession::from_seed(1, [0x22; 32]).unwrap();
    let (party, contribution) = ThresholdParty::join(&keygen, 0, &params).unwrap();
    let mut coordinator = KeygenCoordinator::new(keygen, params.clone());
    coordinator.accept(contribution).unwrap();
    drop(party);
    let collective = coordinator.finish().unwrap();

    let ingress = OrderIngressSession::new([0x32; 32], 4, &params, &collective).unwrap();
    let trader_keys = [
        SigningKey::from_bytes(&[0x51; 32]),
        SigningKey::from_bytes(&[0x52; 32]),
        SigningKey::from_bytes(&[0x53; 32]),
        SigningKey::from_bytes(&[0x54; 32]),
    ];
    let source_verifier = SigningKey::from_bytes(&[0x61; 32]);
    let orders = [
        PrivateOrder::bid(1, 3),
        PrivateOrder::bid(2, 2),
        PrivateOrder::ask(1, 1),
        PrivateOrder::ask(2, 3),
    ];
    let mut source_book = AuthenticatedOrderBook::new(
        ingress.clone(),
        trader_keys
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
    )
    .unwrap();
    let batch = ExactBatchKeyV1::new([0x81; 32], [0x82; 32], 3, 22, [0x83; 32]);
    let mut openings = Vec::new();
    for slot in 0..4usize {
        let seed = [0x71 + slot as u8; 32];
        let submission = SignedOrderSubmission::encrypt_and_sign_private_book_row(
            &ingress,
            slot,
            7 + slot as u64,
            orders[slot],
            seed,
            &params,
            &collective,
            &trader_keys[slot],
        )
        .unwrap();
        let binding = source_book
            .accept_private_book_opened(submission, orders[slot], seed, &params, &collective)
            .unwrap();
        let actor = [0x41 + slot as u8; 32];
        let source = binding.certify_for_market(&actor, &source_verifier);
        let side = match source.side() {
            fhegg_fhe::Side::Bid => OpeningSideV1::Bid,
            fhegg_fhe::Side::Ask => OpeningSideV1::Ask,
        };
        openings.push(
            BazaarOpeningCertificateV1::issue(
                ExactEnvelopeStatementV1::new(
                    actor,
                    19,
                    batch.federation_id(),
                    batch.content_session(),
                    batch.content_epoch(),
                    batch.batch_id(),
                    batch.source_root(),
                    [0x90 + slot as u8; 32],
                    source.ciphertext_digest(),
                    source.message_digest(),
                ),
                OpeningOrderV1::new(
                    slot as u8,
                    side,
                    source.qty().try_into().unwrap(),
                    source.limit().try_into().unwrap(),
                )
                .unwrap(),
                source,
                &source_verifier,
            )
            .unwrap(),
        );
    }
    let root = [
        1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 5, 0, 0, 0, 6, 0, 0, 0, 7, 0, 0, 0, 8, 0,
        0, 0,
    ];
    let book = ExactBookBindingV1::new(19, batch, batch, root).unwrap();
    let certificate = BazaarExchangeOpeningCertificateV1::issue(
        [0xc1; 32],
        [0xc2; 32],
        [0xc3; 32],
        ExactOrdinaryUnitKeyV1::new([0xa1; 32], [0xa2; 32], 447, 0),
        ExactOrdinaryUnitKeyV1::new([0xb1; 32], [0xb2; 32], 812, 3),
        book,
        openings.try_into().unwrap(),
        &source_verifier,
    )
    .unwrap();
    let decoded =
        BazaarExchangeOpeningCertificateV1::from_wire_bytes(&certificate.to_wire_bytes()).unwrap();
    let verified = decoded.verify(&source_verifier.verifying_key()).unwrap();
    assert_eq!(verified.book(), book);
    assert_eq!(verified.openings().len(), 4);
    assert_eq!(verified.offered().part(), 447);
    assert_eq!(verified.requested().part(), 812);
}
