//! **The ORACLE WELD over REAL hardware attestation.**
//!
//! Drives [`GradedMark::from_tee_attested`] against the genuine captured AWS Nitro attestation
//! document (`us-east-1` `c5.xlarge` debug enclave, `user_data = [0xAB; 32]`) — the same fixture
//! `attested_data_lane.rs` and `nitro_real.rs` verify. This proves the graded-mark TEE lane rides
//! REAL vendor crypto (COSE_Sign1 ES384 + X.509 chain to the pinned AWS Nitro root G1), not a mock.
//!
//! ## What this fixture can and cannot carry (stated honestly)
//!
//! The captured enclave bound an opaque 32-byte commitment (`[0xAB; 32]`), NOT a decimal price —
//! that is what the real hardware signed, and we do not fabricate a price fixture. So over the REAL
//! doc this test proves the two teeth that DO fire on genuine crypto:
//!
//! 1. the underlying attestation is genuine ([`attest_data`] succeeds over it), and
//! 2. `GradedMark::from_tee_attested` over that genuine attestation is REFUSED with
//!    [`MarkError::PriceDecode`] — because `[0xAB; 32]` is not a clean price. The lending consumer
//!    can NEVER be fed a mark that is not a decoded price, even from a genuine enclave.
//!
//! The POSITIVE pole (a genuine attestation over a real decimal-price payload mints a graded mark)
//! is proven both polarities in the `oracle_mark` unit tests over the SAME injected
//! `TeeAttestationVerifier` seam whose vendor crypto is proven real here — the fixture attests a
//! commitment, the production feed attests a price, one seam.

use dregg_cell::tee_attest::TeeQuoteKind;
use dregg_tee_verify::{
    attest_data, verify_nitro_core, AttestedDataInput, GradedMark, MarkError, NitroVerifier,
    PayloadBinding,
};

const REAL_DOC: &[u8] = include_bytes!("data/nitro_att.bin");
/// The 32 bytes the live enclave really bound into `user_data`.
const BOUND: [u8; 32] = [0xABu8; 32];

fn pinned_measurement() -> [u8; 32] {
    verify_nitro_core(REAL_DOC)
        .expect("the real Nitro fixture verifies")
        .0
        .measurement
}

fn real_input<'a>(payload: &'a [u8]) -> AttestedDataInput<'a> {
    AttestedDataInput {
        kind: TeeQuoteKind::AwsNitro,
        attestation: REAL_DOC,
        payload,
        binding: PayloadBinding::Raw32,
        expected_measurement: pinned_measurement(),
    }
}

#[test]
fn the_real_attestation_under_the_graded_mark_is_genuine() {
    // The attestation itself is real vendor crypto: attest_data mints a fact over the genuine doc.
    let verifier = NitroVerifier::without_freshness();
    let fact = attest_data(&verifier, &real_input(&BOUND))
        .expect("the genuine AWS Nitro attestation verifies");
    assert_eq!(fact.measurement, pinned_measurement());
    assert_eq!(fact.report_data, BOUND);
}

#[test]
fn a_genuine_non_price_attestation_yields_no_mark() {
    // REAL-CRYPTO TOOTH: the attestation is genuine, but the enclave bound a 32-byte commitment,
    // not a price → the graded-mark decode gate refuses it. Not a crypto failure — a price-shape
    // failure over real hardware attestation.
    let verifier = NitroVerifier::without_freshness();
    let err = GradedMark::from_tee_attested(&verifier, &real_input(&BOUND)).unwrap_err();
    assert!(
        matches!(err, MarkError::PriceDecode(_)),
        "a genuine attestation over a non-price payload must be refused by the decode gate, got {err:?}"
    );
}

#[test]
fn a_forged_attestation_yields_no_mark_over_real_crypto() {
    // Corrupt the signed bytes → the vendor crypto refuses → no fact → no mark.
    let verifier = NitroVerifier::without_freshness();
    let mut doc = REAL_DOC.to_vec();
    let mid = doc.len() / 2;
    doc[mid] ^= 0xFF;
    let input = AttestedDataInput {
        kind: TeeQuoteKind::AwsNitro,
        attestation: &doc,
        payload: &BOUND,
        binding: PayloadBinding::Raw32,
        expected_measurement: pinned_measurement(),
    };
    let err = GradedMark::from_tee_attested(&verifier, &input).unwrap_err();
    assert!(
        matches!(err, MarkError::Attestation(_)),
        "a tampered doc must be refused by the vendor crypto before any price decode, got {err:?}"
    );
}
