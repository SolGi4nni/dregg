//! **The REAL zkTLS oracle-fact verifier, homed** — the host-side crypto seam
//! `dregg-cell` fails closed without.
//!
//! `dregg-cell` ships only the *shape* of a web-oracle fact: the
//! [`OracleFactVerifier`](dregg_cell::oracle_attest::OracleFactVerifier) trait and a
//! fail-closed [`OracleWitnessedPredicateVerifier`](dregg_cell::oracle_attest) that
//! rejects every proof until a genuine verifier is installed. This module IS that
//! genuine verifier: [`ZkOracleFactVerifier`] decodes a portable oracle-fact proof,
//! authenticates it with the REAL `tlsn` MPC-TLS 2PC presentation verifier
//! ([`verify_zkoracle_live_host`]) against a pinned server + a pinned notary key, and
//! only then yields the [`OracleFactClaims`] the light-client check compares against a
//! pinned fact identity.
//!
//! It is homed HERE (a `zkoracle-prove` consumer already, behind the same `zk-live`
//! feature that pulls the heavy `tlsn` backend) rather than in a detached crate: this
//! crate is a root-workspace member and so inherits the workspace `[patch]` tables the
//! `tlsn` / ark-serialize / plonky3 fork graph resolves under — a detached crate does
//! not, and misresolves.
//!
//! ## The honest boundary (same as `dregg_cell::oracle_attest`)
//!
//! Accepting a fact proves **a named TLS server, authenticated by the public web PKI +
//! the pinned notary, sent bytes committing to [`attestation_commitment`]** — a single
//! oracle-root web-fact, NOT a trustless or true-answer claim. Verification is
//! fail-closed: any failure of the real `tlsn` `presentation.verify()` (tampered /
//! forged presentation, wrong server pin, wrong / unpinned notary, or — as for a modeled
//! default attestation — no live presentation at all) surfaces as `Err`, so the claims
//! are returned ONLY for a genuinely authenticated live proof.

use dregg_cell::oracle_attest::{OracleFactClaims, OracleFactVerifier};
use dregg_zkoracle_prove::ZkOracleAttestation;
use dregg_zkoracle_prove::attestation::verify_zkoracle_live_host;
use serde::{Deserialize, Serialize};

use crate::attest::attestation_commitment;

/// The portable oracle-fact proof the verifier decodes — the three things
/// [`verify_zkoracle_live_host`] needs, in one bincode blob a caller carries on the
/// action's witness:
///
/// - `server` — the pinned HTTPS host the presentation must authenticate the session to;
/// - `attestation` — the serializable [`ZkOracleAttestation`] (its
///   [`ZkOracleAttestation::tlsn_presentation`] carries the REAL `tlsn` `Presentation`
///   bytes the live verifier checks);
/// - `notary_key` — the bincode of the pinned notary `tlsn` `VerifyingKey` (the SAME
///   `(presentation bytes, bincode notary key)` split the `dregg-oracle` envelope uses),
///   deserialized to the real key type and passed as the out-of-band trust anchor.
#[derive(Clone, Serialize, Deserialize)]
pub struct OracleFactProof {
    /// The pinned HTTPS server the session is authenticated to (e.g. `api.coinbase.com`).
    pub server: String,
    /// The serializable zkOracle attestation carrying the live `tlsn` presentation.
    pub attestation: ZkOracleAttestation,
    /// Bincode of the pinned notary `tlsn::attestation::signing::VerifyingKey`.
    pub notary_key: Vec<u8>,
}

impl OracleFactProof {
    /// Assemble a proof from its parts. `notary_key` is the bincode of the pinned notary
    /// `tlsn` `VerifyingKey` (as `dregg_zkoracle_prove::notary_server::verifying_key_of`
    /// then `bincode::serialize` yields).
    pub fn new(
        server: impl Into<String>,
        attestation: ZkOracleAttestation,
        notary_key: Vec<u8>,
    ) -> Self {
        OracleFactProof {
            server: server.into(),
            attestation,
            notary_key,
        }
    }

    /// Encode to the `proof_bytes` an [`OracleFactVerifier`] consumes.
    pub fn encode(&self) -> Result<Vec<u8>, String> {
        bincode::serialize(self).map_err(|e| format!("encode oracle-fact proof: {e}"))
    }
}

/// The genuine host-side zkTLS oracle-fact verifier. Install it into `dregg-cell`'s
/// fail-closed seam with
/// `OracleWitnessedPredicateVerifier::with_verifier(Arc::new(ZkOracleFactVerifier))`.
#[derive(Clone, Copy, Debug, Default)]
pub struct ZkOracleFactVerifier;

impl OracleFactVerifier for ZkOracleFactVerifier {
    fn verify_fact(&self, proof_bytes: &[u8]) -> Result<OracleFactClaims, String> {
        // 1. Decode the portable proof (server + attestation + bincode notary key).
        let proof: OracleFactProof = bincode::deserialize(proof_bytes)
            .map_err(|e| format!("decode oracle-fact proof: {e}"))?;
        let notary_key: tlsn::attestation::signing::VerifyingKey =
            bincode::deserialize(&proof.notary_key)
                .map_err(|e| format!("decode notary verifying key: {e}"))?;

        // 2. Authenticate with the REAL tlsn presentation verifier against the pinned
        //    server + pinned notary. Fail-closed: any failure (tampered / forged / wrong
        //    server / wrong notary / no live presentation) returns Err, so we NEVER yield
        //    claims for an unauthenticated proof.
        let verified = verify_zkoracle_live_host(&proof.attestation, &proof.server, &notary_key)
            .map_err(|e| format!("zkoracle live-host verification failed: {e}"))?;

        // 3. The commitment is the canonical fingerprint of the authenticated attestation
        //    — the SAME 32 bytes a minted R2 turn witnesses, recomputed here so the
        //    light-client check can compare it against the pinned fact identity.
        let commitment = attestation_commitment(&proof.attestation);

        Ok(OracleFactClaims {
            commitment,
            // The authenticated server name (yielded by the real presentation verify),
            // not merely the requested pin.
            server: verified.session.server_name,
            // Reaching here means every leg validated; a policy rejection would have
            // surfaced as Err above.
            ok: true,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::attest::AttestationCarrier;
    use dregg_zkoracle_prove::notary_server::{generate_notary_key, verifying_key_of};

    /// A modeled fixture proof: a genuine modeled attestation (its `tlsn_presentation` is
    /// `None`) + a real, freshly-generated pinned notary key, bincode-encoded into the
    /// portable proof shape. The wire round-trips; the live verifier fails closed on it
    /// (no real `tlsn` presentation to authenticate) — the happy accept path needs a real
    /// hosted-notary MPC-TLS roundtrip (the named operational remainder).
    fn fixture_proof() -> OracleFactProof {
        let carrier = AttestationCarrier::default();
        let (att, _field) = carrier
            .attest_turn("done — a modeled, benign confined turn.")
            .expect("a benign turn is attestable");
        let sk = generate_notary_key().expect("generate a notary signing key");
        let vk = verifying_key_of(&sk).expect("derive the tlsn verifying key");
        let notary_key = bincode::serialize(&vk).expect("bincode the notary verifying key");
        OracleFactProof::new("api.coinbase.com", att, notary_key)
    }

    #[test]
    fn proof_wire_roundtrips() {
        let proof = fixture_proof();
        let bytes = proof.encode().expect("encode");
        let back: OracleFactProof = bincode::deserialize(&bytes).expect("decode");
        assert_eq!(back.server, "api.coinbase.com");
        assert_eq!(back.notary_key, proof.notary_key);
        // The notary key round-trips back to a real tlsn VerifyingKey.
        let _vk: tlsn::attestation::signing::VerifyingKey =
            bincode::deserialize(&back.notary_key).expect("notary key decodes");
    }

    #[test]
    fn modeled_attestation_fails_closed() {
        // A modeled attestation carries no live tlsn presentation → the real live-host
        // verifier refuses, so verify_fact returns Err (NEVER Ok claims).
        let bytes = fixture_proof().encode().expect("encode");
        let res = ZkOracleFactVerifier.verify_fact(&bytes);
        assert!(
            res.is_err(),
            "modeled (no-live-presentation) proof must fail closed"
        );
    }

    #[test]
    fn garbage_bytes_rejected() {
        let res = ZkOracleFactVerifier.verify_fact(b"not a valid oracle-fact proof");
        assert!(res.is_err(), "undecodable proof bytes must be rejected");
    }
}
