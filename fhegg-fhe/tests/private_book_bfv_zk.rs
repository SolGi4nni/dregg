//! Heavy hostile gate for transferable private-root/BFV same-opening evidence.
//!
//! This target must be routed to the release-only `heavy` nextest profile when
//! the module is integrated.  The fixed n=4096 R1CS is intentionally far too
//! large for the default development loop.

use dregg_circuit_prove::dark_bazaar_private::{statement, PrivateBookWitness, PrivateOrder};
use fhegg_fhe::bfv_lean::FOLD_MODULI;
use fhegg_fhe::private_book_bfv_zk::{
    prove_private_book_bfv_native_slice_zk, prove_private_book_bfv_zk,
    verify_private_book_bfv_native_slice_zk, verify_private_book_bfv_zk,
    PrivateBookBfvNativeSliceProof, PrivateBookBfvZkProof,
};
use fhegg_fhe::private_book_relation::{
    encrypt_private_book, PrivateBookCiphertexts, PrivateBookEncryptionOpening,
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
    (parties, coordinator.finish().expect("collective key"))
}

fn fixture() -> (PrivateBookWitness, PrivateBookEncryptionOpening) {
    let witness = PrivateBookWitness::try_from_orders_with_blinding(
        &[
            PrivateOrder::bid(10, 2),
            PrivateOrder::bid(6, 1),
            PrivateOrder::ask(5, 0),
            PrivateOrder::ask(8, 1),
        ],
        core::array::from_fn(|lane| 17_000 + lane as u32),
    )
    .expect("private book");
    let opening =
        PrivateBookEncryptionOpening::from_seeds([[0x31; 32], [0x32; 32], [0x33; 32], [0x34; 32]]);
    (witness, opening)
}

#[test]
fn proof_wire_is_bounded_versioned_and_fail_closed() {
    assert!(PrivateBookBfvZkProof::from_bytes(b"").is_err());
    assert!(PrivateBookBfvZkProof::from_bytes(b"FHPZK999\0\0\0\0\0\0").is_err());

    let mut oversized = Vec::from(&b"FHPZK001"[..]);
    oversized.extend_from_slice(&1u16.to_be_bytes());
    oversized.extend_from_slice(&(65_537u32).to_be_bytes());
    oversized.resize(14 + 65_537, 0);
    assert!(PrivateBookBfvZkProof::from_bytes(&oversized).is_err());
}

/// One proof plus four full hostile verifier reconstructions is minutes-class
/// even in release.  The entire binary belongs in nextest's heavy-only set.
#[test]
fn exact_pk_bfv_and_poseidon_relation_refuses_every_public_substitution() {
    let params = BfvParams::fold_set();
    let key_session = KeygenSession::from_seed(2, [0x41; 32]).expect("key session");
    let (_parties, public_key) = collective_keygen(&key_session, &params);
    let (witness, opening) = fixture();
    let public = statement(0xDBA2, &witness).expect("private statement");
    let ciphertexts =
        encrypt_private_book(&witness, &opening, &params, &public_key).expect("BFV book");

    let proof = prove_private_book_bfv_zk(
        public,
        &witness,
        &ciphertexts,
        &opening,
        &params,
        &public_key,
    )
    .expect("transferable proof");
    let proof = PrivateBookBfvZkProof::from_bytes(&proof.to_bytes()).expect("proof round trip");
    verify_private_book_bfv_zk(&proof, public, &ciphertexts, &params, &public_key)
        .expect("honest proof");

    let other_session = KeygenSession::from_seed(2, [0x42; 32]).expect("other key session");
    let (_other_parties, other_key) = collective_keygen(&other_session, &params);
    assert!(verify_private_book_bfv_zk(&proof, public, &ciphertexts, &params, &other_key).is_err());

    let mut wrong_ciphertexts = ciphertexts.rows().clone();
    wrong_ciphertexts[0].polys[0].rows[0][0] =
        (wrong_ciphertexts[0].polys[0].rows[0][0] + 1) % FOLD_MODULI[0];
    assert!(verify_private_book_bfv_zk(
        &proof,
        public,
        &PrivateBookCiphertexts::from_rows(wrong_ciphertexts),
        &params,
        &public_key,
    )
    .is_err());

    let mut wrong_root = public;
    wrong_root.order_root[0] ^= 1;
    assert!(
        verify_private_book_bfv_zk(&proof, wrong_root, &ciphertexts, &params, &public_key,)
            .is_err()
    );

    let mut wrong_session = public;
    wrong_session.session += 1;
    assert!(
        verify_private_book_bfv_zk(&proof, wrong_session, &ciphertexts, &params, &public_key,)
            .is_err()
    );

    // Modulus and plaintext-layout drift fail before the proof system is even
    // entered; neither is accepted as a caller-selectable statement knob.
    let mut wrong_modulus = ciphertexts.rows().clone();
    wrong_modulus[0].moduli[0] ^= 2;
    assert!(verify_private_book_bfv_zk(
        &proof,
        public,
        &PrivateBookCiphertexts::from_rows(wrong_modulus),
        &params,
        &public_key,
    )
    .is_err());

    let mut wrong_layout = ciphertexts.rows().clone();
    wrong_layout[0].plain_bound -= 1;
    assert!(verify_private_book_bfv_zk(
        &proof,
        public,
        &PrivateBookCiphertexts::from_rows(wrong_layout),
        &params,
        &public_key,
    )
    .is_err());
}

/// The native-PQ cut proves one full 4,096-term equation and the complete
/// private-book/root relation through the Lean descriptor.  This is a heavy
/// production-backend test, intentionally sharing this binary's release-only
/// nextest routing.
#[test]
fn native_pq_exact_slice_proves_real_fixture_and_refuses_public_substitution() {
    let params = BfvParams::fold_set();
    let key_session = KeygenSession::from_seed(2, [0x61; 32]).expect("key session");
    let (_parties, public_key) = collective_keygen(&key_session, &params);
    let (witness, opening) = fixture();
    let public = statement(0xDBA2, &witness).expect("private statement");
    let ciphertexts =
        encrypt_private_book(&witness, &opening, &params, &public_key).expect("BFV book");

    let proof = prove_private_book_bfv_native_slice_zk(
        public,
        &witness,
        &ciphertexts,
        &opening,
        &params,
        &public_key,
    )
    .expect("native exact-slice proof");
    let proof =
        PrivateBookBfvNativeSliceProof::from_postcard(&proof.to_postcard().expect("proof encode"))
            .expect("proof decode");
    verify_private_book_bfv_native_slice_zk(&proof, public, &ciphertexts, &params, &public_key)
        .expect("honest native exact slice");

    let other_session = KeygenSession::from_seed(2, [0x62; 32]).expect("other key session");
    let (_other_parties, other_key) = collective_keygen(&other_session, &params);
    assert!(verify_private_book_bfv_native_slice_zk(
        &proof,
        public,
        &ciphertexts,
        &params,
        &other_key,
    )
    .is_err());

    let mut wrong_ciphertexts = ciphertexts.rows().clone();
    wrong_ciphertexts[0].polys[0].rows[0][0] =
        (wrong_ciphertexts[0].polys[0].rows[0][0] + 1) % FOLD_MODULI[0];
    assert!(verify_private_book_bfv_native_slice_zk(
        &proof,
        public,
        &PrivateBookCiphertexts::from_rows(wrong_ciphertexts),
        &params,
        &public_key,
    )
    .is_err());

    let mut wrong_root = public;
    wrong_root.order_root[7] ^= 1;
    assert!(verify_private_book_bfv_native_slice_zk(
        &proof,
        wrong_root,
        &ciphertexts,
        &params,
        &public_key,
    )
    .is_err());
}
