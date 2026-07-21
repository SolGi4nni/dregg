//! Hostile teeth for the exact BFV/private-root witness relation.
//!
//! This target belongs with the proof-heavy private-clearing gates once the
//! module is wired into `fhegg-fhe`'s `amm-input-binding` feature.

use dregg_circuit_prove::dark_bazaar_private::{statement, PrivateBookWitness, PrivateOrder, Side};
use ed25519_dalek::SigningKey;
use fhe::bfv::Ciphertext;
use fhe_traits::{DeserializeParametrized, Serialize as FheSerialize};
use fhegg_fhe::attestation::InputDigest;
use fhegg_fhe::order_ingress::{
    AuthenticatedOrderBook, OrderIngressSession, SignedOrderSubmission,
};
use fhegg_fhe::private_book_relation::{
    encrypt_private_book, fold_private_book_ciphertexts, private_book_relation_digest,
    verify_private_book_opening, FoldedPrivateBookCiphertext, PrivateBookCiphertexts,
    PrivateBookEncryptionOpening, PRIVATE_BOOK_PUBLIC_BOUND,
};
use fhegg_fhe::threshold::{
    BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, ThresholdParty,
};

fn collective_keygen(
    session: &KeygenSession,
    params: &BfvParams,
) -> (Vec<ThresholdParty>, CollectivePublicKey) {
    let mut coordinator = KeygenCoordinator::new(session.clone(), params.clone());
    let mut parties = Vec::with_capacity(session.n_parties());
    for party in 0..session.n_parties() {
        let (state, contribution) =
            ThresholdParty::join(session, party, params).expect("party keygen");
        coordinator
            .accept(contribution)
            .expect("ordered contribution");
        parties.push(state);
    }
    let collective = coordinator.finish().expect("complete collective keygen");
    (parties, collective)
}

fn fixture() -> (PrivateBookWitness, PrivateBookEncryptionOpening) {
    let witness = PrivateBookWitness::try_from_orders_with_blinding(
        &[
            PrivateOrder::bid(10, 2),
            PrivateOrder::bid(6, 1),
            PrivateOrder::ask(5, 0),
            PrivateOrder::ask(8, 1),
        ],
        core::array::from_fn(|lane| 777 + lane as u32),
    )
    .expect("fixed private book");
    let opening =
        PrivateBookEncryptionOpening::from_seeds([[0x11; 32], [0x22; 32], [0x33; 32], [0x44; 32]]);
    (witness, opening)
}

#[test]
fn exact_bfv_rows_open_the_same_private_root_and_refuse_every_substitution() {
    let params = BfvParams::fold_set();
    let session = KeygenSession::from_seed(2, [0x51; 32]).expect("keygen session");
    let (parties, public_key) = collective_keygen(&session, &params);
    // Keep custody live for the duration of the test; this relation never asks
    // it for a decryption or secret-share accessor.
    let _parties: Vec<ThresholdParty> = parties;

    let (witness, opening) = fixture();
    let public = statement(0xDBA2, &witness).expect("private statement");
    let ciphertexts =
        encrypt_private_book(&witness, &opening, &params, &public_key).expect("BFV book");
    verify_private_book_opening(
        public,
        &witness,
        &ciphertexts,
        &opening,
        &params,
        &public_key,
    )
    .expect("exact relation");

    let mut wrong_order = witness.clone();
    wrong_order.orders[0].qty -= 1;
    assert!(verify_private_book_opening(
        public,
        &wrong_order,
        &ciphertexts,
        &opening,
        &params,
        &public_key,
    )
    .is_err());

    let mut wrong_root = public;
    wrong_root.order_root[0] ^= 1;
    assert!(verify_private_book_opening(
        wrong_root,
        &witness,
        &ciphertexts,
        &opening,
        &params,
        &public_key,
    )
    .is_err());

    let wrong_opening =
        PrivateBookEncryptionOpening::from_seeds([[0x11; 32], [0x22; 32], [0x33; 32], [0x45; 32]]);
    assert!(verify_private_book_opening(
        public,
        &witness,
        &ciphertexts,
        &wrong_opening,
        &params,
        &public_key,
    )
    .is_err());

    let mut reordered = ciphertexts.rows().clone();
    reordered.swap(0, 1);
    assert!(verify_private_book_opening(
        public,
        &witness,
        &PrivateBookCiphertexts::from_rows(reordered),
        &opening,
        &params,
        &public_key,
    )
    .is_err());

    let other_session = KeygenSession::from_seed(2, [0x52; 32]).expect("other session");
    let (_other_parties, other_key) = collective_keygen(&other_session, &params);
    assert!(verify_private_book_opening(
        public,
        &witness,
        &ciphertexts,
        &opening,
        &params,
        &other_key,
    )
    .is_err());

    let digest = private_book_relation_digest(public, &ciphertexts, &params, &public_key);
    let mut tampered_rows = ciphertexts.rows().clone();
    tampered_rows[0] = tampered_rows[1].clone();
    assert_ne!(
        digest,
        private_book_relation_digest(
            public,
            &PrivateBookCiphertexts::from_rows(tampered_rows),
            &params,
            &public_key,
        )
    );
}

#[test]
fn metadata_slot_keeps_zero_quantity_side_and_limit_injective() {
    let params = BfvParams::fold_set();
    let session = KeygenSession::from_seed(1, [0x61; 32]).expect("keygen session");
    let (_parties, public_key) = collective_keygen(&session, &params);
    let blind = core::array::from_fn(|lane| 91 + lane as u32);
    let opening =
        PrivateBookEncryptionOpening::from_seeds([[0x71; 32], [0x72; 32], [0x73; 32], [0x74; 32]]);
    let bid_zero =
        PrivateBookWitness::try_from_orders_with_blinding(&[PrivateOrder::bid(0, 0)], blind)
            .expect("zero bid");
    let ask_zero = PrivateBookWitness::try_from_orders_with_blinding(
        &[PrivateOrder {
            side: Side::Ask,
            qty: 0,
            limit: 3,
        }],
        blind,
    )
    .expect("zero ask");
    let bid_ciphertexts =
        encrypt_private_book(&bid_zero, &opening, &params, &public_key).expect("zero bid rows");
    let ask_ciphertexts =
        encrypt_private_book(&ask_zero, &opening, &params, &public_key).expect("zero ask rows");

    // Unary quantity lanes are all zero in both books.  The exact canonical
    // ciphertext still differs because encrypted slot 8 retains the root's
    // seven-bit order code.
    assert_ne!(
        bid_ciphertexts.rows()[0].to_fhe_bytes(),
        ask_ciphertexts.rows()[0].to_fhe_bytes()
    );
}

#[test]
fn duplicate_bfv_randomness_is_refused_before_encryption() {
    let params = BfvParams::fold_set();
    let session = KeygenSession::from_seed(1, [0x81; 32]).expect("keygen session");
    let (_parties, public_key) = collective_keygen(&session, &params);
    let (witness, _) = fixture();
    let duplicate = PrivateBookEncryptionOpening::from_seeds([[0x99; 32]; 4]);
    assert!(encrypt_private_book(&witness, &duplicate, &params, &public_key).is_err());
}

#[test]
fn packed_fold_consumes_the_exact_proof_rows_and_refuses_a_detached_shape() {
    let params = BfvParams::fold_set();
    let session = KeygenSession::from_seed(1, [0x91; 32]).expect("keygen session");
    let (_parties, public_key) = collective_keygen(&session, &params);
    let (witness, opening) = fixture();
    let ciphertexts =
        encrypt_private_book(&witness, &opening, &params, &public_key).expect("private rows");

    let folded = fold_private_book_ciphertexts(&ciphertexts, &params).expect("exact packed fold");
    assert_eq!(FoldedPrivateBookCiphertext::demand_slots(), 0..4);
    assert_eq!(FoldedPrivateBookCiphertext::supply_slots(), 4..8);
    assert_eq!(FoldedPrivateBookCiphertext::metadata_slot(), 8);
    assert_eq!(
        folded.ciphertext().plain_bound,
        PRIVATE_BOOK_PUBLIC_BOUND * 4
    );

    // Independent native-BFV addition oracle: the packed consumer adds the
    // exact four proof-row wires, without re-encryption or a side-specific row.
    let mut expected = Ciphertext::from_bytes(&ciphertexts.rows()[0].to_fhe_bytes(), params.arc())
        .expect("row zero parses");
    for row in &ciphertexts.rows()[1..] {
        let row = Ciphertext::from_bytes(&row.to_fhe_bytes(), params.arc()).expect("row parses");
        expected += &row;
    }
    assert_eq!(folded.ciphertext().to_fhe_bytes(), expected.to_bytes());

    let mut detached = ciphertexts.rows().clone();
    detached[2].plain_bound = 1;
    assert!(
        fold_private_book_ciphertexts(&PrivateBookCiphertexts::from_rows(detached), &params)
            .is_err()
    );
}

#[test]
fn authenticated_ingress_emits_the_exact_proof_ciphertext_not_a_second_encoding() {
    let params = BfvParams::fold_set();
    let session = KeygenSession::from_seed(1, [0xA1; 32]).expect("keygen session");
    let (_parties, public_key) = collective_keygen(&session, &params);
    let ingress = OrderIngressSession::new([0xA2; 32], 4, &params, &public_key)
        .expect("private ingress session");
    let trader_key = SigningKey::from_bytes(&[0xA3; 32]);
    let private_order = PrivateOrder::ask(1, 2);
    let seed = [0xA4; 32];

    let submission = SignedOrderSubmission::encrypt_and_sign_private_book_row(
        &ingress,
        0,
        7,
        private_order,
        seed,
        &params,
        &public_key,
        &trader_key,
    )
    .expect("exact private row submission");
    let submitted_input = InputDigest::ciphertext(submission.ciphertext());

    let witness = PrivateBookWitness::try_from_orders_with_blinding(
        &[private_order],
        core::array::from_fn(|lane| 101 + lane as u32),
    )
    .expect("matching private book");
    let opening =
        PrivateBookEncryptionOpening::from_seeds([seed, [0xA5; 32], [0xA6; 32], [0xA7; 32]]);
    let proof_rows =
        encrypt_private_book(&witness, &opening, &params, &public_key).expect("proof rows");
    assert_eq!(
        submitted_input,
        InputDigest::ciphertext(&proof_rows.rows()[0])
    );

    let mut wrong =
        AuthenticatedOrderBook::new(ingress.clone(), vec![trader_key.verifying_key().to_bytes()])
            .expect("authenticated book");
    assert!(
        wrong
            .accept_private_book_opened(
                submission.clone(),
                private_order,
                [0xA8; 32],
                &params,
                &public_key,
            )
            .is_err(),
        "detached BFV randomness must fail before consuming the source sequence"
    );

    let binding = wrong
        .accept_private_book_opened(submission, private_order, seed, &params, &public_key)
        .expect("exact row opening and trader signature");
    assert_eq!(binding.ciphertext_digest(), submitted_input.digest);
    let inputs = wrong
        .finish_private_book_source_inputs()
        .expect("no legacy side-specific row retyping");
    assert_eq!(inputs.len(), 2);
    assert_eq!(inputs[1], submitted_input);

    let second_key = SigningKey::from_bytes(&[0xA9; 32]);
    let mut reused = AuthenticatedOrderBook::new(
        ingress.clone(),
        vec![
            trader_key.verifying_key().to_bytes(),
            second_key.verifying_key().to_bytes(),
        ],
    )
    .expect("two-trader book");
    let first = SignedOrderSubmission::encrypt_and_sign_private_book_row(
        &ingress,
        0,
        11,
        private_order,
        seed,
        &params,
        &public_key,
        &trader_key,
    )
    .expect("first row");
    reused
        .accept_private_book_opened(first, private_order, seed, &params, &public_key)
        .expect("first seed accepted");
    let other_order = PrivateOrder::bid(1, 3);
    let second = SignedOrderSubmission::encrypt_and_sign_private_book_row(
        &ingress,
        1,
        11,
        other_order,
        seed,
        &params,
        &public_key,
        &second_key,
    )
    .expect("second row uses same randomness");
    assert!(matches!(
        reused.accept_private_book_opened(second, other_order, seed, &params, &public_key),
        Err(fhegg_fhe::order_ingress::OrderIngressError::DuplicatePrivateBookEncryptionSeed)
    ));
}
