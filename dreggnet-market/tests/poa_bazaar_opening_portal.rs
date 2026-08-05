#![cfg(feature = "private-attested-clearing")]

use dregg_circuit_prove::dark_bazaar_private::PrivateOrder;
use dreggnet_market::poa_bazaar_opening_portal::{
    BazaarExchangeOpeningCertificateV1, BazaarOpeningCertificateV1, BazaarOpeningError,
    ExactBatchKeyV1, ExactBookBindingV1, ExactEnvelopeStatementV1, ExactOrdinaryUnitKeyV1,
    OpeningOrderV1, OpeningSideV1,
};
use ed25519_dalek::SigningKey;
use fhegg_fhe::order_ingress::{
    AuthenticatedOrderBook, OrderIngressSession, OrderSourceCertificate, SignedOrderSubmission,
};
use fhegg_fhe::threshold::{
    BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, ThresholdParty,
};
fn collective_key(params: &BfvParams, seed: [u8; 32]) -> CollectivePublicKey {
    let session = KeygenSession::from_seed(1, seed).unwrap();
    let (party, contribution) = ThresholdParty::join(&session, 0, params).unwrap();
    let mut coordinator = KeygenCoordinator::new(session, params.clone());
    coordinator.accept(contribution).unwrap();
    drop(party);
    coordinator.finish().unwrap()
}

struct Fixture {
    source_verifier: SigningKey,
    source: OrderSourceCertificate,
    statement: ExactEnvelopeStatementV1,
    order: OpeningOrderV1,
}

fn fixture() -> Fixture {
    let params = BfvParams::fold_set();
    let collective = collective_key(&params, [0x21; 32]);
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
    Fixture {
        source_verifier,
        source,
        statement,
        order,
    }
}

struct ExchangeFixture {
    source_verifier: SigningKey,
    book: ExactBookBindingV1,
    openings: [BazaarOpeningCertificateV1; 4],
    offered: ExactOrdinaryUnitKeyV1,
    requested: ExactOrdinaryUnitKeyV1,
}

fn exchange_fixture(ingress_nonce: [u8; 32]) -> ExchangeFixture {
    let params = BfvParams::fold_set();
    let collective = collective_key(&params, [0x22; 32]);
    let ingress = OrderIngressSession::new(ingress_nonce, 4, &params, &collective).unwrap();
    let trader_keys = [
        SigningKey::from_bytes(&[0x51; 32]),
        SigningKey::from_bytes(&[0x52; 32]),
        SigningKey::from_bytes(&[0x53; 32]),
        SigningKey::from_bytes(&[0x54; 32]),
    ];
    let source_verifier = SigningKey::from_bytes(&[0x61; 32]);
    let private_orders = [
        PrivateOrder::bid(1, 3),
        PrivateOrder::bid(2, 2),
        PrivateOrder::ask(1, 1),
        PrivateOrder::ask(2, 3),
    ];
    let mut book = AuthenticatedOrderBook::new(
        ingress.clone(),
        trader_keys
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
    )
    .unwrap();
    let batch_key = ExactBatchKeyV1::new([0x81; 32], [0x82; 32], 3, 22, [0x83; 32]);
    let mut openings = Vec::new();
    for slot in 0..4usize {
        let seed = [0x71 + slot as u8; 32];
        let submission = SignedOrderSubmission::encrypt_and_sign_private_book_row(
            &ingress,
            slot,
            7 + slot as u64,
            private_orders[slot],
            seed,
            &params,
            &collective,
            &trader_keys[slot],
        )
        .unwrap();
        let binding = book
            .accept_private_book_opened(
                submission,
                private_orders[slot],
                seed,
                &params,
                &collective,
            )
            .unwrap();
        let actor = [0x41 + slot as u8; 32];
        let source = binding.certify_for_market(&actor, &source_verifier);
        let statement = ExactEnvelopeStatementV1::new(
            actor,
            19,
            batch_key.federation_id(),
            batch_key.content_session(),
            batch_key.content_epoch(),
            batch_key.batch_id(),
            batch_key.source_root(),
            [0x90 + slot as u8; 32],
            source.ciphertext_digest(),
            source.message_digest(),
        );
        let side = match source.side() {
            fhegg_fhe::Side::Bid => OpeningSideV1::Bid,
            fhegg_fhe::Side::Ask => OpeningSideV1::Ask,
        };
        openings.push(
            BazaarOpeningCertificateV1::issue(
                statement,
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
    let private_root = [
        1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 5, 0, 0, 0, 6, 0, 0, 0, 7, 0, 0, 0, 8, 0,
        0, 0,
    ];
    ExchangeFixture {
        source_verifier,
        book: ExactBookBindingV1::new(19, batch_key, batch_key, private_root).unwrap(),
        openings: openings.try_into().unwrap(),
        offered: ExactOrdinaryUnitKeyV1::new([0xa1; 32], [0xa2; 32], 447, 0),
        requested: ExactOrdinaryUnitKeyV1::new([0xb1; 32], [0xb2; 32], 812, 3),
    }
}

#[test]
fn exact_opening_certificate_roundtrips_and_verifies_the_full_statement() {
    let fixture = fixture();
    let certificate = BazaarOpeningCertificateV1::issue(
        fixture.statement.clone(),
        fixture.order,
        fixture.source,
        &fixture.source_verifier,
    )
    .unwrap();
    let wire = certificate.to_wire_bytes();
    let decoded = BazaarOpeningCertificateV1::from_wire_bytes(&wire).unwrap();
    assert_eq!(decoded, certificate);

    let verified = decoded
        .verify(&fixture.source_verifier.verifying_key())
        .unwrap();
    assert_eq!(verified.statement(), &fixture.statement);
    assert_eq!(verified.order(), fixture.order);
    assert_eq!(
        verified.source_binding_digest(),
        certificate.source().binding_digest()
    );

    let statement_wire = fixture.statement.to_wire_bytes();
    assert_eq!(
        ExactEnvelopeStatementV1::from_wire_bytes(&statement_wire).unwrap(),
        fixture.statement
    );
    assert_eq!(statement_wire, fixture.statement.to_wire_bytes());
}

#[test]
fn issuance_refuses_actor_order_slot_ciphertext_and_signature_substitution() {
    let fixture = fixture();
    let wrong_actor = ExactEnvelopeStatementV1::new(
        [0x99; 32],
        fixture.statement.round(),
        fixture.statement.federation_id(),
        fixture.statement.content_session(),
        fixture.statement.content_epoch(),
        fixture.statement.batch_id(),
        fixture.statement.source_root(),
        fixture.statement.nullifier(),
        fixture.statement.ciphertext_commitment(),
        fixture.statement.signature_commitment(),
    );
    assert_eq!(
        BazaarOpeningCertificateV1::issue(
            wrong_actor,
            fixture.order,
            fixture.source.clone(),
            &fixture.source_verifier,
        ),
        Err(BazaarOpeningError::ActorMismatch)
    );

    let wrong_slot = OpeningOrderV1::new(1, OpeningSideV1::Bid, 1, 3).unwrap();
    assert_eq!(
        BazaarOpeningCertificateV1::issue(
            fixture.statement.clone(),
            wrong_slot,
            fixture.source.clone(),
            &fixture.source_verifier,
        ),
        Err(BazaarOpeningError::SlotMismatch)
    );

    for wrong_order in [
        OpeningOrderV1::new(0, OpeningSideV1::Ask, 1, 3).unwrap(),
        OpeningOrderV1::new(0, OpeningSideV1::Bid, 2, 3).unwrap(),
        OpeningOrderV1::new(0, OpeningSideV1::Bid, 1, 2).unwrap(),
    ] {
        assert_eq!(
            BazaarOpeningCertificateV1::issue(
                fixture.statement.clone(),
                wrong_order,
                fixture.source.clone(),
                &fixture.source_verifier,
            ),
            Err(BazaarOpeningError::OrderMismatch)
        );
    }

    let wrong_ciphertext = ExactEnvelopeStatementV1::new(
        fixture.statement.actor(),
        fixture.statement.round(),
        fixture.statement.federation_id(),
        fixture.statement.content_session(),
        fixture.statement.content_epoch(),
        fixture.statement.batch_id(),
        fixture.statement.source_root(),
        fixture.statement.nullifier(),
        [0x98; 32],
        fixture.statement.signature_commitment(),
    );
    assert_eq!(
        BazaarOpeningCertificateV1::issue(
            wrong_ciphertext,
            fixture.order,
            fixture.source.clone(),
            &fixture.source_verifier,
        ),
        Err(BazaarOpeningError::CiphertextCommitmentMismatch)
    );

    let wrong_signature = ExactEnvelopeStatementV1::new(
        fixture.statement.actor(),
        fixture.statement.round(),
        fixture.statement.federation_id(),
        fixture.statement.content_session(),
        fixture.statement.content_epoch(),
        fixture.statement.batch_id(),
        fixture.statement.source_root(),
        fixture.statement.nullifier(),
        fixture.statement.ciphertext_commitment(),
        [0x97; 32],
    );
    assert_eq!(
        BazaarOpeningCertificateV1::issue(
            wrong_signature,
            fixture.order,
            fixture.source,
            &fixture.source_verifier,
        ),
        Err(BazaarOpeningError::SignatureCommitmentMismatch)
    );
}

#[test]
fn signed_round_batch_nullifier_and_order_coordinates_cannot_be_replayed() {
    let fixture = fixture();
    let certificate = BazaarOpeningCertificateV1::issue(
        fixture.statement,
        fixture.order,
        fixture.source,
        &fixture.source_verifier,
    )
    .unwrap();
    let wire = certificate.to_wire_bytes();
    // The outer header is 12 bytes. Within the statement: round starts at 42,
    // batch id at 122, nullifier at 162. The order follows the 258-byte statement.
    for offset in [12 + 42, 12 + 122, 12 + 162, 12 + 258] {
        let mut substituted = wire.clone();
        substituted[offset] ^= 1;
        let decoded = BazaarOpeningCertificateV1::from_wire_bytes(&substituted).unwrap();
        assert!(
            decoded
                .verify(&fixture.source_verifier.verifying_key())
                .is_err()
        );
    }

    let wrong_key = SigningKey::from_bytes(&[0xa1; 32]);
    assert!(certificate.verify(&wrong_key.verifying_key()).is_err());
}

#[test]
fn strict_decoder_refuses_version_lengths_tags_truncation_and_trailing_bytes() {
    let fixture = fixture();
    let certificate = BazaarOpeningCertificateV1::issue(
        fixture.statement,
        fixture.order,
        fixture.source,
        &fixture.source_verifier,
    )
    .unwrap();
    let wire = certificate.to_wire_bytes();

    let mut version = wire.clone();
    version[9] = 2;
    assert_eq!(
        BazaarOpeningCertificateV1::from_wire_bytes(&version),
        Err(BazaarOpeningError::UnsupportedVersion)
    );

    let mut statement_len = wire.clone();
    statement_len[11] ^= 1;
    assert!(matches!(
        BazaarOpeningCertificateV1::from_wire_bytes(&statement_len),
        Err(BazaarOpeningError::MalformedWire("statement length"))
    ));

    let mut order_tag = wire.clone();
    order_tag[12 + 258 + 1] = 9;
    assert!(matches!(
        BazaarOpeningCertificateV1::from_wire_bytes(&order_tag),
        Err(BazaarOpeningError::MalformedWire("order side"))
    ));

    assert!(BazaarOpeningCertificateV1::from_wire_bytes(&wire[..wire.len() - 1]).is_err());
    let mut trailing = wire;
    trailing.push(0);
    assert!(matches!(
        BazaarOpeningCertificateV1::from_wire_bytes(&trailing),
        Err(BazaarOpeningError::MalformedWire("trailing bytes"))
    ));

    assert!(OpeningOrderV1::new(4, OpeningSideV1::Bid, 1, 3).is_err());
    assert!(OpeningOrderV1::new(0, OpeningSideV1::Bid, 0, 3).is_err());
    assert!(OpeningOrderV1::new(0, OpeningSideV1::Bid, 16, 3).is_err());
    assert!(OpeningOrderV1::new(0, OpeningSideV1::Bid, 1, 4).is_err());
}

#[test]
fn ordinary_exchange_roundtrips_as_one_exact_four_opening_book() {
    let fixture = exchange_fixture([0x31; 32]);
    let mut shuffled = fixture.openings.clone();
    shuffled.swap(0, 3);
    let certificate = BazaarExchangeOpeningCertificateV1::issue(
        [0xc1; 32],
        [0xc2; 32],
        [0xc3; 32],
        fixture.offered,
        fixture.requested,
        fixture.book,
        shuffled,
        &fixture.source_verifier,
    )
    .unwrap();
    assert_eq!(
        certificate
            .openings()
            .iter()
            .map(|opening| opening.order().slot())
            .collect::<Vec<_>>(),
        vec![0, 1, 2, 3],
        "the transferable wire has one canonical slot order",
    );

    let wire = certificate.to_wire_bytes();
    let decoded = BazaarExchangeOpeningCertificateV1::from_wire_bytes(&wire).unwrap();
    assert_eq!(decoded, certificate);
    assert_eq!(decoded.to_wire_bytes(), wire);
    let verified = decoded
        .verify(&fixture.source_verifier.verifying_key())
        .unwrap();
    assert_eq!(verified.exchange_id(), [0xc1; 32]);
    assert_eq!(verified.seller(), [0xc2; 32]);
    assert_eq!(verified.buyer(), [0xc3; 32]);
    assert_eq!(verified.offered(), fixture.offered);
    assert_eq!(verified.requested(), fixture.requested);
    assert_eq!(verified.book(), fixture.book);
    assert_eq!(verified.openings().len(), 4);
    assert_ne!(verified.book_binding_digest(), [0; 32]);
}

#[test]
fn exchange_binding_refuses_cross_book_cross_opening_and_unit_substitution() {
    let fixture = exchange_fixture([0x31; 32]);
    let different_session = exchange_fixture([0x32; 32]);

    let mut mixed_openings = fixture.openings.clone();
    mixed_openings[2] = different_session.openings[2].clone();
    assert_eq!(
        BazaarExchangeOpeningCertificateV1::issue(
            [0xc1; 32],
            [0xc2; 32],
            [0xc3; 32],
            fixture.offered,
            fixture.requested,
            fixture.book,
            mixed_openings,
            &fixture.source_verifier,
        ),
        Err(BazaarOpeningError::OpeningSessionMismatch)
    );

    let wrong_batch = ExactBatchKeyV1::new([0x81; 32], [0x82; 32], 3, 23, [0x83; 32]);
    let wrong_book = ExactBookBindingV1::new(
        fixture.book.round(),
        wrong_batch,
        wrong_batch,
        fixture.book.private_book_commitment(),
    )
    .unwrap();
    assert_eq!(
        BazaarExchangeOpeningCertificateV1::issue(
            [0xc1; 32],
            [0xc2; 32],
            [0xc3; 32],
            fixture.offered,
            fixture.requested,
            wrong_book,
            fixture.openings.clone(),
            &fixture.source_verifier,
        ),
        Err(BazaarOpeningError::BookBatchMismatch)
    );

    let certificate = BazaarExchangeOpeningCertificateV1::issue(
        [0xc1; 32],
        [0xc2; 32],
        [0xc3; 32],
        fixture.offered,
        fixture.requested,
        fixture.book,
        fixture.openings,
        &fixture.source_verifier,
    )
    .unwrap();
    let mut substituted = certificate.to_wire_bytes();
    // Header/privacy + exchange/seller/buyer + ordinary tag + receipt/source.
    let offered_part_offset = 8 + 2 + 1 + 32 * 3 + 1 + 32 + 32;
    substituted[offered_part_offset] ^= 1;
    let decoded = BazaarExchangeOpeningCertificateV1::from_wire_bytes(&substituted).unwrap();
    assert!(matches!(
        decoded.verify(&fixture.source_verifier.verifying_key()),
        Err(BazaarOpeningError::InvalidExchangeSignature)
    ));
}

#[test]
fn exchange_wire_refuses_relic_house_blind_noncanonical_root_and_malleability() {
    let fixture = exchange_fixture([0x31; 32]);
    let another_batch = ExactBatchKeyV1::new([0x81; 32], [0x82; 32], 3, 23, [0x83; 32]);
    assert_eq!(
        ExactBookBindingV1::new(
            fixture.book.round(),
            fixture.book.batch_key(),
            another_batch,
            fixture.book.private_book_commitment(),
        ),
        Err(BazaarOpeningError::BookClaimMismatch)
    );
    assert_eq!(
        BazaarExchangeOpeningCertificateV1::issue(
            [0xc1; 32],
            [0xc2; 32],
            [0xc2; 32],
            fixture.offered,
            fixture.requested,
            fixture.book,
            fixture.openings.clone(),
            &fixture.source_verifier,
        ),
        Err(BazaarOpeningError::SameParty)
    );
    assert_eq!(
        BazaarExchangeOpeningCertificateV1::issue(
            [0xc1; 32],
            [0xc2; 32],
            [0xc3; 32],
            fixture.offered,
            fixture.offered,
            fixture.book,
            fixture.openings.clone(),
            &fixture.source_verifier,
        ),
        Err(BazaarOpeningError::SameUnit)
    );
    let certificate = BazaarExchangeOpeningCertificateV1::issue(
        [0xc1; 32],
        [0xc2; 32],
        [0xc3; 32],
        fixture.offered,
        fixture.requested,
        fixture.book,
        fixture.openings,
        &fixture.source_verifier,
    )
    .unwrap();
    let wire = certificate.to_wire_bytes();

    let mut house_blind = wire.clone();
    house_blind[10] = 1;
    assert_eq!(
        BazaarExchangeOpeningCertificateV1::from_wire_bytes(&house_blind),
        Err(BazaarOpeningError::HouseBlindUnsupported)
    );

    let mut relic = wire.clone();
    relic[8 + 2 + 1 + 32 * 3] = 1;
    assert_eq!(
        BazaarExchangeOpeningCertificateV1::from_wire_bytes(&relic),
        Err(BazaarOpeningError::RelicIngressUnsupported)
    );

    let batch = fixture.book.batch_key();
    assert_eq!(
        ExactBookBindingV1::new(
            fixture.book.round(),
            batch,
            batch,
            BABYBEAR_NONCANONICAL_ROOT,
        ),
        Err(BazaarOpeningError::NonCanonicalPrivateRoot)
    );

    assert!(BazaarExchangeOpeningCertificateV1::from_wire_bytes(&wire[..wire.len() - 1]).is_err());
    let mut trailing = wire;
    trailing.push(0);
    assert!(matches!(
        BazaarExchangeOpeningCertificateV1::from_wire_bytes(&trailing),
        Err(BazaarOpeningError::MalformedWire(
            "exchange certificate trailing bytes"
        ))
    ));
}

const BABYBEAR_NONCANONICAL_ROOT: [u8; 32] = [
    1, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0,
];
