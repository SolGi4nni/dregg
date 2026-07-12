//! **The REAL TEE attestation-fact verifier, homed** — the host-side vendor-crypto
//! seam `dregg-cell` fails closed without (the TEE twin of [`crate::oracle_fact`]).
//!
//! `dregg-cell` ships only the *shape* of a TEE fact: the
//! [`TeeAttestationVerifier`](dregg_cell::tee_attest::TeeAttestationVerifier) trait
//! and a fail-closed
//! [`TeeWitnessedPredicateVerifier`](dregg_cell::tee_attest::TeeWitnessedPredicateVerifier)
//! that rejects every quote until a genuine verifier is installed. This module IS
//! that install: [`TeeFactVerifier`] dispatches a quote by its
//! [`TeeQuoteKind`] byte to the real vendor path — `dregg-tee-verify`'s
//! [`NitroVerifier`] (COSE_Sign1 signature + X.509 chain to the pinned AWS Nitro
//! root G1) or [`SnpVerifier`] (report-body ECDSA-P384 under VCEK ← ASK ← the
//! pinned AMD ARK; fail-closed until roots are pinned) — and
//! [`install_tee_fact_verifier`] registers it in a
//! [`WitnessedPredicateRegistry`] under [`tee_predicate_vk`] via `register_custom`,
//! exactly the install `cell/src/tee_attest.rs` names.
//!
//! ## The honest boundary (same as `dregg_cell::tee_attest`)
//!
//! Accepting a TEE fact proves **single-hardware-root execution-integrity**: the
//! measured binary ran inside a genuine enclave and bound the landed turn/session
//! commitment into the quote's `report_data`. You trust the CPU vendor's
//! attestation root; it is not trustless and says nothing about the *output*'s
//! correctness. Verification is fail-closed end to end: an unknown kind byte, a
//! vendor path with no pinned roots, a broken chain/signature, a wrong
//! measurement, or an unbound `report_data` each surface as a refusal — claims are
//! yielded ONLY for a genuinely vendor-signed quote.

use std::sync::Arc;

use dregg_cell::predicate::WitnessedPredicateRegistry;
use dregg_cell::tee_attest::{
    TeeAttestationVerifier, TeeQuoteKind, TeeReportClaims, TeeWitnessedPredicateVerifier,
    tee_predicate_vk,
};
use dregg_tee_verify::{NitroVerifier, SnpVerifier};

/// The genuine host-side TEE-fact verifier: one installed object that dispatches
/// on the quote's kind byte to the real vendor verifier. Both arms are REAL and
/// fail-closed — there is no accept path that skips vendor crypto.
pub struct TeeFactVerifier {
    /// AWS Nitro path: chain to the pinned AWS root G1 (embedded in tee-verify).
    nitro: NitroVerifier,
    /// AMD SEV-SNP path: `SnpVerifier::new()` has NO pinned AMD roots and rejects
    /// every report; upgrade with [`TeeFactVerifier::with_snp`].
    snp: SnpVerifier,
}

impl TeeFactVerifier {
    /// The production shape: Nitro with the default freshness window, SNP
    /// fail-closed until AMD roots are pinned via [`Self::with_snp`].
    pub fn new() -> TeeFactVerifier {
        TeeFactVerifier {
            nitro: NitroVerifier::new(),
            snp: SnpVerifier::new(),
        }
    }

    /// Crypto-only Nitro verification (no wall-clock freshness bound) — for
    /// captured fixture documents, or when freshness is enforced by a nonce bound
    /// into the `report_data` commitment upstream. The signature/chain teeth are
    /// unchanged.
    pub fn without_freshness() -> TeeFactVerifier {
        TeeFactVerifier {
            nitro: NitroVerifier::without_freshness(),
            snp: SnpVerifier::new(),
        }
    }

    /// Install a pinned-root SNP verifier (e.g.
    /// `SnpVerifier::with_pinned_roots_pem(ark, ask)?.with_min_tcb(min)`) for the
    /// SEV-SNP dispatch arm.
    pub fn with_snp(mut self, snp: SnpVerifier) -> TeeFactVerifier {
        self.snp = snp;
        self
    }
}

impl Default for TeeFactVerifier {
    fn default() -> Self {
        Self::new()
    }
}

impl TeeAttestationVerifier for TeeFactVerifier {
    fn verify_report(
        &self,
        kind: TeeQuoteKind,
        report_bytes: &[u8],
    ) -> Result<TeeReportClaims, String> {
        match kind {
            TeeQuoteKind::AwsNitro => self.nitro.verify_report(kind, report_bytes),
            TeeQuoteKind::SevSnp => self.snp.verify_report(kind, report_bytes),
            other => Err(format!(
                "no verifier wired for TEE quote kind {other:?} (fail-closed)"
            )),
        }
    }
}

/// Install `verifier` as THE TEE-fact verifier in `registry`: wrap it in the
/// fail-closed [`TeeWitnessedPredicateVerifier`] and register under
/// [`tee_predicate_vk`] — after this, every
/// `WitnessedPredicateKind::Custom { vk_hash: tee_predicate_vk() }` predicate the
/// registry verifies runs REAL vendor crypto (and before it, the kind is simply
/// not registered: refused).
pub fn install_tee_fact_verifier(
    registry: &mut WitnessedPredicateRegistry,
    verifier: Arc<dyn TeeAttestationVerifier>,
) {
    registry.register_custom(
        tee_predicate_vk(),
        Arc::new(TeeWitnessedPredicateVerifier::with_verifier(verifier)),
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::predicate::{InputRef, PredicateInput, WitnessedPredicateError};
    use dregg_cell::tee_attest::{encode_tee_proof, tee_attestation_predicate};
    use dregg_tee_verify::verify_nitro_core;

    /// The REAL captured live-enclave Nitro document (us-east-1 c5.xlarge debug
    /// enclave, `user_data = [0xAB; 32]`) — the same fixture tee-verify pins.
    const REAL_DOC: &[u8] = include_bytes!("../../tee-verify/tests/data/nitro_att.bin");
    /// The commitment that enclave really bound.
    const BOUND: [u8; 32] = [0xAB; 32];

    fn registry_with_real_tee() -> WitnessedPredicateRegistry {
        let mut registry = WitnessedPredicateRegistry::empty();
        install_tee_fact_verifier(
            &mut registry,
            Arc::new(TeeFactVerifier::without_freshness()),
        );
        registry
    }

    #[test]
    fn the_installed_registry_accepts_the_real_nitro_fact_and_pins_teeth() {
        let (claims, _) = verify_nitro_core(REAL_DOC).expect("fixture verifies");
        let predicate = tee_attestation_predicate(claims.measurement, 8);
        assert!(matches!(predicate.input_ref, InputRef::Slot { index: 8 }));
        let proof = encode_tee_proof(TeeQuoteKind::AwsNitro, REAL_DOC);
        let registry = registry_with_real_tee();

        // Accept: pinned measurement + the slot the enclave really bound.
        registry
            .verify(&predicate, &PredicateInput::Slot(&BOUND), &proof)
            .expect("a genuine quote for the pinned binary + bound slot is accepted");

        // Wrong pinned measurement → refused.
        let wrong_binary = tee_attestation_predicate([0u8; 32], 8);
        assert!(
            registry
                .verify(&wrong_binary, &PredicateInput::Slot(&BOUND), &proof)
                .is_err()
        );

        // A slot value the quote did not bind → refused (replayed/unbound quote).
        assert!(
            registry
                .verify(&predicate, &PredicateInput::Slot(&[0x11u8; 32]), &proof)
                .is_err()
        );

        // A tampered signed byte → the vendor crypto refuses.
        let mut tampered = REAL_DOC.to_vec();
        let mid = tampered.len() / 2;
        tampered[mid] ^= 0xFF;
        let tampered_proof = encode_tee_proof(TeeQuoteKind::AwsNitro, &tampered);
        assert!(
            registry
                .verify(&predicate, &PredicateInput::Slot(&BOUND), &tampered_proof)
                .is_err()
        );
    }

    #[test]
    fn an_uninstalled_registry_refuses_even_a_genuine_quote() {
        let (claims, _) = verify_nitro_core(REAL_DOC).expect("fixture verifies");
        let predicate = tee_attestation_predicate(claims.measurement, 8);
        let proof = encode_tee_proof(TeeQuoteKind::AwsNitro, REAL_DOC);
        let err = WitnessedPredicateRegistry::empty()
            .verify(&predicate, &PredicateInput::Slot(&BOUND), &proof)
            .unwrap_err();
        assert!(matches!(
            err,
            WitnessedPredicateError::KindNotRegistered { .. }
        ));
    }

    #[test]
    fn the_snp_arm_fails_closed_until_amd_roots_are_pinned() {
        // A structurally-plausible-length blob is still refused: no pinned ARK/ASK.
        let fake_snp_report = vec![0u8; 1184];
        let err = TeeFactVerifier::new()
            .verify_report(TeeQuoteKind::SevSnp, &fake_snp_report)
            .unwrap_err();
        assert!(!err.is_empty());

        // And unwired kinds are refused outright.
        assert!(
            TeeFactVerifier::new()
                .verify_report(TeeQuoteKind::IntelTdx, b"whatever")
                .is_err()
        );
    }
}
