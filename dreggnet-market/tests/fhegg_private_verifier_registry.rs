//! Hostile reconstruction gate for the frontend-neutral fhEgg verifier registry.

#![cfg(all(feature = "private-attested-clearing", feature = "fhegg-settlement"))]

use dregg_circuit_prove::dark_bazaar_private::{
    self, PrivateBookWitness, PrivateOrder, PublicStatement,
};
use dreggnet_market::DarkBazaarOffering;
use dreggnet_market::fhegg_verifier_registry::{
    FheggVerifierRegistryError, FheggVerifierRegistryKind, PrivateBfvHostedVerifierConfig,
};
use dreggnet_market::private_attested_clearing::PrivateAttestedClearingPolicy;
use dreggnet_market::private_bfv_attested_clearing::{
    PrivateBfvAttestedClearingVerifier, PrivateBfvAttestedVerifierConfigError,
};
use dreggnet_offerings::{Offering, SessionConfig};
use ed25519_dalek::SigningKey;
use fhegg_fhe::attestation::{
    AuthenticatedQuorumVerifier, BfvPublicIdentity, ComputationIntegrityVerifier, Digest32,
    InputDigest,
};
use fhegg_fhe::bfv_lean::FOLD_MODULI;
use fhegg_fhe::private_book_relation::{
    PrivateBookCiphertexts, PrivateBookEncryptionOpening, encrypt_private_book,
};
use fhegg_fhe::threshold::{
    BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, ThresholdParty,
};

struct Fixture {
    ordered_public_keys: Vec<[u8; 32]>,
    threshold: usize,
    value_bits: u32,
    bfv: BfvPublicIdentity,
    claim_nonce: Digest32,
    statement: PublicStatement,
    params: BfvParams,
    public_key: CollectivePublicKey,
    ciphertexts: PrivateBookCiphertexts,
    source_inputs: Vec<InputDigest>,
    pinned_verifier_id: Digest32,
}

fn collective_key(seed: [u8; 32], params: &BfvParams) -> (KeygenSession, CollectivePublicKey) {
    let session = KeygenSession::from_seed(2, seed).expect("public DKG session");
    let mut coordinator = KeygenCoordinator::new(session.clone(), params.clone());
    for party in 0..session.n_parties() {
        let (secret_party, contribution) =
            ThresholdParty::join(&session, party, params).expect("party-local keygen");
        coordinator
            .accept(contribution)
            .expect("ordered public contribution");
        drop(secret_party);
    }
    (
        session,
        coordinator.finish().expect("collective public key"),
    )
}

fn fixture() -> Fixture {
    let signing_keys = [
        SigningKey::from_bytes(&[0x31; 32]),
        SigningKey::from_bytes(&[0x32; 32]),
    ];
    let ordered_public_keys = signing_keys
        .iter()
        .map(|key| key.verifying_key().to_bytes())
        .collect::<Vec<_>>();
    let threshold = 2;
    let value_bits = 16;
    let params = BfvParams::fold_set();
    let (keygen, public_key) = collective_key([0x41; 32], &params);
    let bfv = BfvPublicIdentity::from_public(&params, &keygen, &public_key);
    let witness = PrivateBookWitness::try_from_orders_with_blinding(
        &[
            PrivateOrder::ask(1, 3),
            PrivateOrder::bid(1, 2),
            PrivateOrder::bid(1, 3),
        ],
        core::array::from_fn(|lane| 23_000 + lane as u32),
    )
    .expect("fixed private book");
    let statement = dark_bazaar_private::statement(0xDBA2, &witness).expect("public statement");
    let opening =
        PrivateBookEncryptionOpening::from_seeds([[0x51; 32], [0x52; 32], [0x53; 32], [0x54; 32]]);
    let ciphertexts =
        encrypt_private_book(&witness, &opening, &params, &public_key).expect("private BFV rows");
    let source_inputs = (0..3)
        .flat_map(|order| {
            [
                InputDigest::commitment([0x61 + order as u8; 32]),
                InputDigest::ciphertext(&ciphertexts.rows()[order]),
            ]
        })
        .collect::<Vec<_>>();
    let claim_nonce = [0x71; 32];
    let quorum =
        AuthenticatedQuorumVerifier::new(ordered_public_keys.clone(), threshold).expect("quorum");
    let policy =
        PrivateAttestedClearingPolicy::new(value_bits, bfv.clone()).expect("private policy");
    let direct = PrivateBfvAttestedClearingVerifier::new_source_bound(
        quorum,
        policy,
        claim_nonce,
        statement,
        params.clone(),
        public_key.clone(),
        ciphertexts.clone(),
        source_inputs.clone(),
    )
    .expect("direct provisioned verifier");

    Fixture {
        ordered_public_keys,
        threshold,
        value_bits,
        bfv,
        claim_nonce,
        statement,
        params,
        public_key,
        ciphertexts,
        source_inputs,
        pinned_verifier_id: direct.verifier_id(),
    }
}

#[allow(clippy::too_many_arguments)]
fn config(
    pinned_verifier_id: Digest32,
    ordered_public_keys: Vec<[u8; 32]>,
    threshold: usize,
    value_bits: u32,
    bfv: BfvPublicIdentity,
    claim_nonce: Digest32,
    statement: PublicStatement,
    params: BfvParams,
    public_key: CollectivePublicKey,
    ciphertexts: PrivateBookCiphertexts,
    source_inputs: Vec<InputDigest>,
) -> PrivateBfvHostedVerifierConfig {
    PrivateBfvHostedVerifierConfig::new(
        pinned_verifier_id,
        ordered_public_keys,
        threshold,
        value_bits,
        bfv,
        claim_nonce,
        statement,
        params,
        public_key,
        ciphertexts,
        source_inputs,
    )
}

fn exact_config(fixture: &Fixture) -> PrivateBfvHostedVerifierConfig {
    config(
        fixture.pinned_verifier_id,
        fixture.ordered_public_keys.clone(),
        fixture.threshold,
        fixture.value_bits,
        fixture.bfv.clone(),
        fixture.claim_nonce,
        fixture.statement,
        fixture.params.clone(),
        fixture.public_key.clone(),
        fixture.ciphertexts.clone(),
        fixture.source_inputs.clone(),
    )
}

fn assert_pin_mismatch(config: PrivateBfvHostedVerifierConfig) {
    assert!(matches!(
        config.install(),
        Err(FheggVerifierRegistryError::VerifierIdMismatch { .. })
    ));
}

#[test]
fn exact_public_config_installs_full_private_verifier_in_hosted_operation_registry() {
    let fixture = fixture();
    let config = exact_config(&fixture);
    assert_eq!(config.pinned_verifier_id(), fixture.pinned_verifier_id);
    let registry = config.install().expect("exact deployment pin reconstructs");
    assert_eq!(
        registry.kind(),
        FheggVerifierRegistryKind::PrivateBfvAttested
    );
    assert_eq!(registry.verifier_id(), fixture.pinned_verifier_id);
    assert!(!registry.verify(&[0; 32], b"digest-only private evidence is forbidden"));

    let offering = DarkBazaarOffering::with_private_bfv_attested_registry(config)
        .expect("host installs full private verifier");
    let session = offering
        .open(SessionConfig::with_seed(0xDBA2_0001))
        .expect("hosted Bazaar session");
    let operations = offering.binary_operations(&session);
    assert_eq!(operations.len(), 1);
    assert_eq!(
        operations[0].name,
        dreggnet_market::fhegg_transport::FHEGG_SETTLEMENT_OPERATION
    );

    // Existing callers retain the exact legacy quorum-only constructor.
    let legacy = DarkBazaarOffering::with_fhegg_quorum(
        fixture.ordered_public_keys.clone(),
        fixture.threshold,
    )
    .expect("legacy quorum registry");
    let legacy_session = legacy
        .open(SessionConfig::with_seed(0xDBA2_0002))
        .expect("legacy Bazaar session");
    assert_eq!(legacy.binary_operations(&legacy_session).len(), 1);
}

#[test]
fn pinned_reconstruction_refuses_every_public_substitution() {
    let fixture = fixture();

    let mut wrong_pin = fixture.pinned_verifier_id;
    wrong_pin[0] ^= 1;
    assert_pin_mismatch(config(
        wrong_pin,
        fixture.ordered_public_keys.clone(),
        fixture.threshold,
        fixture.value_bits,
        fixture.bfv.clone(),
        fixture.claim_nonce,
        fixture.statement,
        fixture.params.clone(),
        fixture.public_key.clone(),
        fixture.ciphertexts.clone(),
        fixture.source_inputs.clone(),
    ));

    let mut wrong_nonce = fixture.claim_nonce;
    wrong_nonce[0] ^= 1;
    assert_pin_mismatch(config(
        fixture.pinned_verifier_id,
        fixture.ordered_public_keys.clone(),
        fixture.threshold,
        fixture.value_bits,
        fixture.bfv.clone(),
        wrong_nonce,
        fixture.statement,
        fixture.params.clone(),
        fixture.public_key.clone(),
        fixture.ciphertexts.clone(),
        fixture.source_inputs.clone(),
    ));

    for mutation in 0..4 {
        let mut statement = fixture.statement;
        match mutation {
            0 => statement.session += 1,
            1 => statement.order_root[0] ^= 1,
            2 => {
                statement.p_star = (statement.p_star + 1) % dark_bazaar_private::PRICE_COUNT as u32
            }
            3 => statement.v_star += 1,
            _ => unreachable!(),
        }
        assert_pin_mismatch(config(
            fixture.pinned_verifier_id,
            fixture.ordered_public_keys.clone(),
            fixture.threshold,
            fixture.value_bits,
            fixture.bfv.clone(),
            fixture.claim_nonce,
            statement,
            fixture.params.clone(),
            fixture.public_key.clone(),
            fixture.ciphertexts.clone(),
            fixture.source_inputs.clone(),
        ));
    }

    let mut wrong_rule = fixture.statement;
    wrong_rule.rule += 1;
    assert!(matches!(
        config(
            fixture.pinned_verifier_id,
            fixture.ordered_public_keys.clone(),
            fixture.threshold,
            fixture.value_bits,
            fixture.bfv.clone(),
            fixture.claim_nonce,
            wrong_rule,
            fixture.params.clone(),
            fixture.public_key.clone(),
            fixture.ciphertexts.clone(),
            fixture.source_inputs.clone(),
        )
        .install(),
        Err(FheggVerifierRegistryError::PrivateBfv(
            PrivateBfvAttestedVerifierConfigError::InvalidStatement
        ))
    ));

    let mut wrong_parameter_identity = fixture.bfv.clone();
    wrong_parameter_identity.moduli_digest[0] ^= 1;
    assert!(matches!(
        config(
            fixture.pinned_verifier_id,
            fixture.ordered_public_keys.clone(),
            fixture.threshold,
            fixture.value_bits,
            wrong_parameter_identity,
            fixture.claim_nonce,
            fixture.statement,
            fixture.params.clone(),
            fixture.public_key.clone(),
            fixture.ciphertexts.clone(),
            fixture.source_inputs.clone(),
        )
        .install(),
        Err(FheggVerifierRegistryError::PrivateBfv(
            PrivateBfvAttestedVerifierConfigError::BfvIdentityMismatch
        ))
    ));

    let mut source_inputs = fixture.source_inputs.clone();
    source_inputs[0] = InputDigest::commitment([0x81; 32]);
    assert_pin_mismatch(config(
        fixture.pinned_verifier_id,
        fixture.ordered_public_keys.clone(),
        fixture.threshold,
        fixture.value_bits,
        fixture.bfv.clone(),
        fixture.claim_nonce,
        fixture.statement,
        fixture.params.clone(),
        fixture.public_key.clone(),
        fixture.ciphertexts.clone(),
        source_inputs,
    ));

    let mut wrong_source_row = fixture.source_inputs.clone();
    wrong_source_row[1] = InputDigest::ciphertext_bytes(b"not one of the four exact proof rows");
    assert!(matches!(
        config(
            fixture.pinned_verifier_id,
            fixture.ordered_public_keys.clone(),
            fixture.threshold,
            fixture.value_bits,
            fixture.bfv.clone(),
            fixture.claim_nonce,
            fixture.statement,
            fixture.params.clone(),
            fixture.public_key.clone(),
            fixture.ciphertexts.clone(),
            wrong_source_row,
        )
        .install(),
        Err(FheggVerifierRegistryError::PrivateBfv(
            PrivateBfvAttestedVerifierConfigError::InvalidSourceInputs
        ))
    ));

    let mut wrong_rows = fixture.ciphertexts.rows().clone();
    wrong_rows[0].polys[0].rows[0][0] = (wrong_rows[0].polys[0].rows[0][0] + 1) % FOLD_MODULI[0];
    let wrong_ciphertexts = PrivateBookCiphertexts::from_rows(wrong_rows);
    let mut rebound_sources = fixture.source_inputs.clone();
    rebound_sources[1] = InputDigest::ciphertext(&wrong_ciphertexts.rows()[0]);
    assert_pin_mismatch(config(
        fixture.pinned_verifier_id,
        fixture.ordered_public_keys.clone(),
        fixture.threshold,
        fixture.value_bits,
        fixture.bfv.clone(),
        fixture.claim_nonce,
        fixture.statement,
        fixture.params.clone(),
        fixture.public_key.clone(),
        wrong_ciphertexts,
        rebound_sources,
    ));

    let (other_keygen, other_key) = collective_key([0x42; 32], &fixture.params);
    let other_bfv = BfvPublicIdentity::from_public(&fixture.params, &other_keygen, &other_key);
    assert!(matches!(
        config(
            fixture.pinned_verifier_id,
            fixture.ordered_public_keys.clone(),
            fixture.threshold,
            fixture.value_bits,
            fixture.bfv.clone(),
            fixture.claim_nonce,
            fixture.statement,
            fixture.params.clone(),
            other_key.clone(),
            fixture.ciphertexts.clone(),
            fixture.source_inputs.clone(),
        )
        .install(),
        Err(FheggVerifierRegistryError::PrivateBfv(
            PrivateBfvAttestedVerifierConfigError::BfvIdentityMismatch
        ))
    ));
    assert_pin_mismatch(config(
        fixture.pinned_verifier_id,
        fixture.ordered_public_keys.clone(),
        fixture.threshold,
        fixture.value_bits,
        other_bfv,
        fixture.claim_nonce,
        fixture.statement,
        fixture.params.clone(),
        other_key,
        fixture.ciphertexts.clone(),
        fixture.source_inputs.clone(),
    ));

    let mut reordered_roster = fixture.ordered_public_keys.clone();
    reordered_roster.swap(0, 1);
    assert_pin_mismatch(config(
        fixture.pinned_verifier_id,
        reordered_roster,
        fixture.threshold,
        fixture.value_bits,
        fixture.bfv.clone(),
        fixture.claim_nonce,
        fixture.statement,
        fixture.params.clone(),
        fixture.public_key.clone(),
        fixture.ciphertexts.clone(),
        fixture.source_inputs.clone(),
    ));
    assert_pin_mismatch(config(
        fixture.pinned_verifier_id,
        fixture.ordered_public_keys.clone(),
        1,
        fixture.value_bits,
        fixture.bfv.clone(),
        fixture.claim_nonce,
        fixture.statement,
        fixture.params.clone(),
        fixture.public_key.clone(),
        fixture.ciphertexts.clone(),
        fixture.source_inputs.clone(),
    ));
    assert_pin_mismatch(config(
        fixture.pinned_verifier_id,
        fixture.ordered_public_keys.clone(),
        fixture.threshold,
        fixture.value_bits + 1,
        fixture.bfv.clone(),
        fixture.claim_nonce,
        fixture.statement,
        fixture.params.clone(),
        fixture.public_key.clone(),
        fixture.ciphertexts.clone(),
        fixture.source_inputs.clone(),
    ));

    let mut mismatched_bfv = fixture.bfv.clone();
    mismatched_bfv.opening_threshold = 1;
    assert!(matches!(
        config(
            fixture.pinned_verifier_id,
            fixture.ordered_public_keys,
            fixture.threshold,
            fixture.value_bits,
            mismatched_bfv,
            fixture.claim_nonce,
            fixture.statement,
            fixture.params,
            fixture.public_key,
            fixture.ciphertexts,
            fixture.source_inputs,
        )
        .install(),
        Err(FheggVerifierRegistryError::RosterBfvMismatch)
    ));
}
