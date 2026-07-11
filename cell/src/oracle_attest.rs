//! zkTLS web-oracle attestation as a dregg-verifiable fact — the "the public web
//! said X" primitive.
//!
//! A zkTLS / DECO-style oracle can produce a **proof about a TLS session**: a
//! succinct statement that a *specific TLS server* (named by hostname) delivered a
//! *specific committed response*, without revealing the full transcript. This module
//! turns that proof into a first-class dregg fact on the **same rail** the TEE
//! attestation facts already ride (see [`crate::tee_attest`]) — a
//! [`WitnessedPredicateKind::Custom`] verifier whose commitment a light client
//! re-checks. So a web-derived fact ("`api.example.com` returned this body") becomes a
//! receipt the owner (or any light client) verifies against the pinned fact identity.
//!
//! ## What it proves, and the honest boundary
//!
//! Accepting an oracle fact proves **a named TLS server, authenticated by the public
//! web PKI, sent bytes that commit to `attestation_commitment`** — bridging an
//! off-chain HTTPS response into a dregg fact with no quorum and no re-execution. It is
//! **single-oracle-root, not trustless**: you trust the zkTLS construction's trust
//! model (a notary and/or the TLS/web PKI root the proof anchors to), and — depending on
//! the scheme — its freshness and non-selective-disclosure caveats. It does NOT prove
//! the *server's* answer is true, only that the server *said it* over an authenticated
//! session. Name it "single-oracle-root web-fact attestation."
//!
//! ## Layering (the same discipline as [`crate::tee_attest`] and the STARK verifiers)
//!
//! `dregg-cell` must stay light — it does NOT link the zkTLS crypto (the notary
//! protocol, TLS transcript parsing, the succinct proof system). So this module holds
//! only the *shape*: the [`OracleFactVerifier`] trait (the injected crypto seam) and a
//! fail-closed [`OracleWitnessedPredicateVerifier`] that rejects every proof until a real
//! verifier is installed by the host (mirrors [`crate::tee_attest`] and
//! [`crate::predicate::NotYetWiredVerifier`]). The real zkTLS verifier —
//! `verify_zkoracle_live_host`, which validates the proof against the oracle's trust
//! anchor and extracts the [`OracleFactClaims`] — lives host-side and installs via
//! [`crate::predicate::WitnessedPredicateRegistry::register_custom`] under
//! [`oracle_predicate_vk`].

use std::sync::Arc;

use crate::predicate::{
    InputRef, PredicateInput, WitnessedPredicate, WitnessedPredicateError, WitnessedPredicateKind,
    WitnessedPredicateVerifier, canonical_predicate_vk,
};

/// The claims a genuine, trust-anchor-verified zkTLS proof yields. The injected
/// [`OracleFactVerifier`] is responsible for having proven the fact authentic (the
/// zkTLS proof validates against the oracle's trust root) BEFORE returning these — a
/// verifier that returns claims from an unvalidated proof is a soundness bug.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OracleFactClaims {
    /// The `attestation_commitment` of the proven fact: the 32-byte identity binding
    /// the committed server response. Compared against the predicate's pinned fact
    /// identity — a proof for a different fact is refused.
    pub commitment: [u8; 32],
    /// The TLS server hostname the proof authenticated the session to (e.g.
    /// `api.example.com`). Carried for audit / host policy; the fail-closed core checks
    /// identity via `commitment`.
    pub server: String,
    /// Whether the proof validated against the oracle's trust anchor under the
    /// verifier's policy. `false` = a well-formed but policy-rejected proof (stale,
    /// wrong anchor, disallowed server) — rejected.
    pub ok: bool,
}

/// The injected crypto seam. The host installs a real implementation
/// (`verify_zkoracle_live_host`) that validates the zkTLS proof against the oracle's
/// trust anchor and extracts [`OracleFactClaims`]. `dregg-cell` ships NO implementation —
/// until one is installed the [`OracleWitnessedPredicateVerifier`] fails closed.
pub trait OracleFactVerifier: Send + Sync {
    /// Validate `proof_bytes` as a genuine zkTLS web-oracle proof (against the oracle's
    /// trust anchor) and extract its claims. `Err` on any failure — an implementation
    /// MUST NOT return `Ok` for an unvalidated proof.
    fn verify_fact(&self, proof_bytes: &[u8]) -> Result<OracleFactClaims, String>;
}

/// The canonical `vk_hash` for the zkTLS oracle-fact predicate. Stable identifier a host
/// registers its real verifier under, and the value pinned in
/// [`WitnessedPredicateKind::Custom`] for every oracle fact.
pub fn oracle_predicate_vk() -> [u8; 32] {
    canonical_predicate_vk(b"dregg-oracle-webfact-verifier-v1")
}

/// Build the [`WitnessedPredicate`] for "a zkTLS oracle proved a web fact whose
/// `attestation_commitment` equals `expected_fact_commitment`." The commitment IS the
/// pinned fact identity; the proof blob rides witness index 0 of the action.
pub fn oracle_webfact_predicate(expected_fact_commitment: [u8; 32]) -> WitnessedPredicate {
    WitnessedPredicate {
        kind: WitnessedPredicateKind::Custom {
            vk_hash: oracle_predicate_vk(),
        },
        commitment: expected_fact_commitment,
        // The fact identity is pinned by `commitment`; the verifier needs no external
        // input binding, so it reads the (unused) witness blob at index 0.
        input_ref: InputRef::Witness { index: 0 },
        // The zkTLS proof blob rides witness index 0 of the action.
        proof_witness_index: 0,
    }
}

/// The [`WitnessedPredicateVerifier`] for zkTLS web-oracle facts. Fail-closed:
/// constructed with no injected [`OracleFactVerifier`] it rejects every proof; the host
/// installs the real zkTLS verifier with [`Self::with_verifier`].
pub struct OracleWitnessedPredicateVerifier {
    inner: Option<Arc<dyn OracleFactVerifier>>,
}

impl OracleWitnessedPredicateVerifier {
    /// A fail-closed verifier (no zkTLS crypto installed — rejects everything).
    pub fn new() -> OracleWitnessedPredicateVerifier {
        OracleWitnessedPredicateVerifier { inner: None }
    }

    /// Install the real zkTLS oracle-fact verifier (`verify_zkoracle_live_host`),
    /// host-side.
    pub fn with_verifier(
        verifier: Arc<dyn OracleFactVerifier>,
    ) -> OracleWitnessedPredicateVerifier {
        OracleWitnessedPredicateVerifier {
            inner: Some(verifier),
        }
    }
}

impl Default for OracleWitnessedPredicateVerifier {
    fn default() -> Self {
        Self::new()
    }
}

impl WitnessedPredicateVerifier for OracleWitnessedPredicateVerifier {
    fn name(&self) -> &'static str {
        "oracle-webfact"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::Custom {
            vk_hash: oracle_predicate_vk(),
        }
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        _input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        // FAIL-CLOSED: no zkTLS verifier installed => reject (mirrors tee_attest and the
        // STARK neighbor-adjacency default). A cluster that has not wired an oracle
        // verifier cannot be tricked into accepting an unvalidated web fact.
        let inner = self
            .inner
            .as_ref()
            .ok_or_else(|| WitnessedPredicateError::Rejected {
                kind_name: "oracle-webfact",
                reason: "no OracleFactVerifier installed (fail-closed)".to_string(),
            })?;

        // The injected verifier validates the zkTLS proof against the oracle's trust
        // anchor and extracts its claims. Any validation failure surfaces here as
        // Rejected.
        let claims =
            inner
                .verify_fact(proof_bytes)
                .map_err(|e| WitnessedPredicateError::Rejected {
                    kind_name: "oracle-webfact",
                    reason: format!("oracle fact verification failed: {e}"),
                })?;

        // The pinned fact identity: the predicate commitment IS the expected
        // `attestation_commitment`. A proof for a different fact is refused.
        if &claims.commitment != commitment {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: "oracle-webfact",
                reason: "attestation_commitment does not match the pinned fact identity"
                    .to_string(),
            });
        }

        if !claims.ok {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: "oracle-webfact",
                reason: "oracle proof did not validate under the verifier's policy".to_string(),
            });
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const C: [u8; 32] = [7u8; 32];

    /// A test double for the injected zkTLS verifier — returns fixed claims for any
    /// proof so the commitment/ok logic can be exercised without real crypto.
    struct MockOracle(OracleFactClaims);
    impl OracleFactVerifier for MockOracle {
        fn verify_fact(&self, _proof_bytes: &[u8]) -> Result<OracleFactClaims, String> {
            Ok(self.0.clone())
        }
    }
    /// A test double that fails validation (an unverifiable/forged proof).
    struct RejectOracle;
    impl OracleFactVerifier for RejectOracle {
        fn verify_fact(&self, _proof_bytes: &[u8]) -> Result<OracleFactClaims, String> {
            Err("proof does not validate against trust anchor".to_string())
        }
    }

    fn claims(commitment: [u8; 32], ok: bool) -> OracleFactClaims {
        OracleFactClaims {
            commitment,
            server: "api.example.com".to_string(),
            ok,
        }
    }

    fn proof() -> Vec<u8> {
        b"zktls-proof-bytes".to_vec()
    }

    #[test]
    fn no_verifier_installed_fails_closed() {
        let v = OracleWitnessedPredicateVerifier::new();
        let err = v
            .verify(&C, &PredicateInput::Bytes(&proof()), &proof())
            .unwrap_err();
        assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
    }

    #[test]
    fn matching_commitment_accepts() {
        let v =
            OracleWitnessedPredicateVerifier::with_verifier(Arc::new(MockOracle(claims(C, true))));
        assert!(
            v.verify(&C, &PredicateInput::Bytes(&proof()), &proof())
                .is_ok()
        );
    }

    #[test]
    fn wrong_commitment_rejected() {
        let v = OracleWitnessedPredicateVerifier::with_verifier(Arc::new(MockOracle(claims(
            [1u8; 32], // not C
            true,
        ))));
        assert!(
            v.verify(&C, &PredicateInput::Bytes(&proof()), &proof())
                .is_err()
        );
    }

    #[test]
    fn ok_false_rejected() {
        let v =
            OracleWitnessedPredicateVerifier::with_verifier(Arc::new(MockOracle(claims(C, false))));
        assert!(
            v.verify(&C, &PredicateInput::Bytes(&proof()), &proof())
                .is_err()
        );
    }

    #[test]
    fn forged_proof_rejected() {
        let v = OracleWitnessedPredicateVerifier::with_verifier(Arc::new(RejectOracle));
        assert!(
            v.verify(&C, &PredicateInput::Bytes(&proof()), &proof())
                .is_err()
        );
    }

    #[test]
    fn kind_matches_registered_vk() {
        let v = OracleWitnessedPredicateVerifier::new();
        assert_eq!(
            v.kind(),
            WitnessedPredicateKind::Custom {
                vk_hash: oracle_predicate_vk()
            }
        );
    }

    #[test]
    fn predicate_builder_pins_fact_commitment() {
        let p = oracle_webfact_predicate(C);
        assert_eq!(p.commitment, C);
        assert!(matches!(p.kind, WitnessedPredicateKind::Custom { .. }));
        assert!(matches!(p.input_ref, InputRef::Witness { index: 0 }));
    }
}
