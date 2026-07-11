//! Executor-path registry dispatch of a TEE attestation fact.
//!
//! This is the integration seam the executor actually walks: a
//! [`WitnessedPredicateRegistry`] with a `Custom { vk_hash }` verifier
//! registered under [`tee_predicate_vk`], and a witnessed-predicate fact
//! verified **through the registry's kind-dispatch** — `registry.get(kind)`
//! resolves the same `Arc<dyn WitnessedPredicateVerifier>` and
//! `registry.verify(&wp, ..)` routes to it by `wp.kind`. Nothing here calls
//! the verifier directly; the point is to prove a TEE fact is verifiable via
//! the *same* registry the `dregg-turn` executor dispatches from.
//!
//! Contrast with `tee_attest.rs`'s unit tests, which drive
//! `TeeWitnessedPredicateVerifier::verify` directly. Those prove the verifier
//! logic; this proves the *routing* — that a `Custom` fact lands on the
//! installed verifier when dispatched by kind.

use std::sync::Arc;

use dregg_cell::predicate::{
    PredicateInput, WitnessedPredicate, WitnessedPredicateError, WitnessedPredicateKind,
    WitnessedPredicateRegistry,
};
use dregg_cell::tee_attest::{
    TeeAttestationVerifier, TeeQuoteKind, TeeReportClaims, TeeWitnessedPredicateVerifier,
    encode_tee_proof, tee_attestation_predicate, tee_predicate_vk,
};

/// The pinned expected code measurement (the predicate commitment).
const MEASUREMENT: [u8; 32] = [7u8; 32];
/// The report_data commitment the fact is bound to (the resolved input).
const REPORT_DATA: [u8; 32] = [9u8; 32];
/// The state slot index the predicate reads its bound commitment from.
const REPORT_DATA_SLOT: u8 = 3;

/// A test double for the injected vendor crypto seam. Returns fixed,
/// pre-authenticated claims for any report — the registry never sees the real
/// SEV-SNP / DCAP parsing, only the claim shape the dispatch carries.
struct MockTee(TeeReportClaims);

impl TeeAttestationVerifier for MockTee {
    fn verify_report(
        &self,
        _kind: TeeQuoteKind,
        _report: &[u8],
    ) -> Result<TeeReportClaims, String> {
        Ok(self.0)
    }
}

/// Build a registry with the real TEE verifier installed under its canonical
/// vk_hash — exactly the `register_custom` install the host performs.
fn registry_with_tee(claims: TeeReportClaims) -> WitnessedPredicateRegistry {
    let mut registry = WitnessedPredicateRegistry::empty();
    registry.register_custom(
        tee_predicate_vk(),
        Arc::new(TeeWitnessedPredicateVerifier::with_verifier(Arc::new(
            MockTee(claims),
        ))),
    );
    registry
}

fn snp_proof() -> Vec<u8> {
    encode_tee_proof(TeeQuoteKind::SevSnp, b"snp-report-bytes")
}

/// The registry resolves the `Custom { vk_hash }` kind to the installed TEE
/// verifier by its vk_hash — the lookup the executor performs before dispatch.
#[test]
fn registry_resolves_custom_tee_verifier_by_vk_hash() {
    let registry = registry_with_tee(TeeReportClaims {
        measurement: MEASUREMENT,
        report_data: REPORT_DATA,
        tcb_ok: true,
    });

    let kind = WitnessedPredicateKind::Custom {
        vk_hash: tee_predicate_vk(),
    };
    let verifier = registry
        .get(kind)
        .expect("registry must resolve the Custom TEE kind to the registered verifier");
    assert_eq!(verifier.kind(), kind);
    assert_eq!(verifier.name(), "tee-attestation");

    // A different (unregistered) vk_hash must NOT resolve — the dispatch is
    // keyed on the exact 32-byte hash, not on the Custom discriminant alone.
    assert!(
        registry
            .get(WitnessedPredicateKind::Custom {
                vk_hash: [0xAAu8; 32],
            })
            .is_none(),
        "an unregistered vk_hash must not resolve to any verifier"
    );
}

/// A well-formed TEE fact whose measurement + report_data match is accepted
/// when verified THROUGH the registry's kind-dispatch (`registry.verify`),
/// not by calling the verifier directly.
#[test]
fn tee_fact_accepted_through_registry_dispatch() {
    let registry = registry_with_tee(TeeReportClaims {
        measurement: MEASUREMENT,
        report_data: REPORT_DATA,
        tcb_ok: true,
    });

    // The fact as the executor would carry it: Custom{tee vk}, commitment =
    // the pinned expected measurement, input pointing at the report_data slot.
    let wp: WitnessedPredicate = tee_attestation_predicate(MEASUREMENT, REPORT_DATA_SLOT);
    assert_eq!(
        wp.kind,
        WitnessedPredicateKind::Custom {
            vk_hash: tee_predicate_vk()
        }
    );

    // The executor resolves input_ref -> PredicateInput before dispatch; here
    // the slot resolves to the bound report_data commitment.
    let input = PredicateInput::Slot(&REPORT_DATA);

    registry
        .verify(&wp, &input, &snp_proof())
        .expect("a matching TEE fact must verify through the registry dispatch");
}

/// A TEE fact whose pinned commitment (expected measurement) does NOT match
/// the quote's measurement is rejected through the same dispatch — the routing
/// carries the reject, it does not swallow it.
#[test]
fn tee_fact_wrong_measurement_rejected_through_registry_dispatch() {
    // The installed verifier's quote measures MEASUREMENT ...
    let registry = registry_with_tee(TeeReportClaims {
        measurement: MEASUREMENT,
        report_data: REPORT_DATA,
        tcb_ok: true,
    });

    // ... but the fact pins a DIFFERENT expected binary as its commitment.
    let wrong_measurement = [1u8; 32];
    assert_ne!(wrong_measurement, MEASUREMENT);
    let wp = tee_attestation_predicate(wrong_measurement, REPORT_DATA_SLOT);
    let input = PredicateInput::Slot(&REPORT_DATA);

    let err = registry
        .verify(&wp, &input, &snp_proof())
        .expect_err("a measurement mismatch must be rejected through the dispatch");
    assert!(
        matches!(err, WitnessedPredicateError::Rejected { .. }),
        "expected a Rejected error, got {err:?}"
    );
}

/// Belt-and-suspenders: the same reject also surfaces when the verifier is
/// pulled via `registry.get(kind)` and invoked — proving the reject is a
/// property of the routed verifier, not of the `verify` convenience wrapper.
#[test]
fn wrong_measurement_rejected_via_resolved_verifier() {
    let registry = registry_with_tee(TeeReportClaims {
        measurement: MEASUREMENT,
        report_data: REPORT_DATA,
        tcb_ok: true,
    });

    let wp = tee_attestation_predicate([1u8; 32], REPORT_DATA_SLOT);
    let verifier = registry
        .get(wp.kind)
        .expect("registry must resolve the registered TEE verifier");
    let input = PredicateInput::Slot(&REPORT_DATA);

    assert!(
        verifier
            .verify(&wp.commitment, &input, &snp_proof())
            .is_err(),
        "the resolved verifier must reject the wrong-measurement fact"
    );
}
