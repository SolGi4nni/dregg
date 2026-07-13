//! **The ATTESTED-DATA lane over REAL hardware attestation.**
//!
//! Drives [`attest_data`] end-to-end against the genuine captured AWS Nitro attestation
//! document (`us-east-1` `c5.xlarge` debug enclave, `user_data = [0xAB; 32]`) — the same
//! fixture `tee-verify` pins and `nitro_real.rs` verifies. This proves the ATTESTED-graded
//! data fact rides REAL vendor crypto (COSE_Sign1 ES384 + X.509 chain to the pinned AWS
//! Nitro root G1), not a mock: a genuine attestation over a payload mints the fact; a
//! tampered payload, a wrong pinned enclave, or a tampered attestation is REFUSED.
//!
//! The enclave bound its 32-byte commitment directly into `user_data`, so this exercises
//! the [`PayloadBinding::Raw32`] mode (the payload IS the 32-byte commitment). The
//! [`PayloadBinding::Sha256`] production mode (a variable-length price/mark hashed into
//! `report_data`) is proven both polarities in the `attested_data` unit tests; its vendor
//! crypto is the SAME injected `TeeAttestationVerifier` seam proven real here.

use dregg_cell::tee_attest::TeeQuoteKind;
use dregg_tee_verify::{
    attest_data, verify_nitro_core, AttestedDataInput, AttestedError, NitroVerifier,
    PayloadBinding, TrustGrade,
};

const REAL_DOC: &[u8] = include_bytes!("data/nitro_att.bin");
/// The 32 bytes the live enclave really bound into `user_data`.
const BOUND: [u8; 32] = [0xABu8; 32];

/// The pinned enclave code identity, read from the genuine doc itself.
fn pinned_measurement() -> [u8; 32] {
    verify_nitro_core(REAL_DOC)
        .expect("the real Nitro fixture verifies")
        .0
        .measurement
}

#[test]
fn real_nitro_attestation_over_a_payload_mints_an_attested_fact() {
    let verifier = NitroVerifier::without_freshness();
    let payload = BOUND; // the enclave bound this 32-byte commitment (Raw32)

    let fact = attest_data(
        &verifier,
        &AttestedDataInput {
            kind: TeeQuoteKind::AwsNitro,
            attestation: REAL_DOC,
            payload: &payload,
            binding: PayloadBinding::Raw32,
            expected_measurement: pinned_measurement(),
        },
    )
    .expect("a genuine Nitro attestation binding this payload mints an ATTESTED fact");

    assert_eq!(fact.grade, TrustGrade::Attested);
    assert_eq!(fact.kind, TeeQuoteKind::AwsNitro);
    assert_eq!(fact.measurement, pinned_measurement());
    assert_eq!(fact.report_data, BOUND);
    assert_eq!(fact.payload, BOUND.to_vec());
    assert!(fact.tcb_ok);
}

#[test]
fn a_tampered_payload_is_refused_as_unbound() {
    let verifier = NitroVerifier::without_freshness();
    // Present a DIFFERENT payload with the same genuine attestation → the commitment the
    // enclave bound ([0xAB;32]) is not the commitment to this payload.
    let mut tampered = BOUND;
    tampered[0] ^= 0xFF;

    let err = attest_data(
        &verifier,
        &AttestedDataInput {
            kind: TeeQuoteKind::AwsNitro,
            attestation: REAL_DOC,
            payload: &tampered,
            binding: PayloadBinding::Raw32,
            expected_measurement: pinned_measurement(),
        },
    )
    .unwrap_err();
    assert_eq!(err, AttestedError::Unbound);
}

#[test]
fn a_wrong_pinned_enclave_is_refused() {
    let verifier = NitroVerifier::without_freshness();
    let err = attest_data(
        &verifier,
        &AttestedDataInput {
            kind: TeeQuoteKind::AwsNitro,
            attestation: REAL_DOC,
            payload: &BOUND,
            binding: PayloadBinding::Raw32,
            expected_measurement: [0u8; 32], // not the enclave that produced this feed
        },
    )
    .unwrap_err();
    assert_eq!(err, AttestedError::Measurement);
}

#[test]
fn a_tampered_attestation_is_refused_by_vendor_crypto() {
    let verifier = NitroVerifier::without_freshness();
    let mut doc = REAL_DOC.to_vec();
    let mid = doc.len() / 2;
    doc[mid] ^= 0xFF; // corrupt the signed bytes

    let err = attest_data(
        &verifier,
        &AttestedDataInput {
            kind: TeeQuoteKind::AwsNitro,
            attestation: &doc,
            payload: &BOUND,
            binding: PayloadBinding::Raw32,
            expected_measurement: pinned_measurement(),
        },
    )
    .unwrap_err();
    assert!(
        matches!(err, AttestedError::Attestation(_)),
        "a tampered doc must be refused by the vendor crypto, got {err:?}"
    );
}

#[test]
fn the_wrong_tee_kind_for_the_nitro_verifier_is_refused() {
    let verifier = NitroVerifier::without_freshness();
    let err = attest_data(
        &verifier,
        &AttestedDataInput {
            kind: TeeQuoteKind::SevSnp, // NitroVerifier handles AwsNitro only
            attestation: REAL_DOC,
            payload: &BOUND,
            binding: PayloadBinding::Raw32,
            expected_measurement: pinned_measurement(),
        },
    )
    .unwrap_err();
    assert!(matches!(err, AttestedError::Attestation(_)));
}
