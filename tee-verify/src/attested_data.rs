//! **The ATTESTED-DATA lane** — the input-integrity half of the dreggfi weld.
//!
//! dregg's ZK proves the *logic*; this lane provides trustworthy *inputs* (a price, a
//! mark, a security-flag record) carried with a **trust grade**. It is the OCIP
//! "ATTESTED" grade made concrete: an offline-checkable fact that binds
//!
//! > *enclave `E` (code identity `measurement`) produced / measured payload `P`*
//!
//! by verifying a hardware TEE attestation ([`NitroVerifier`](crate::NitroVerifier),
//! real + fixture-proven; [`SnpVerifier`](crate::SnpVerifier), fail-closed until AMD
//! roots are pinned) whose `report_data` is the caller-chosen **commitment** to `P`.
//!
//! ## What the primitive checks (fail-closed, in order)
//!
//! [`attest_data`] takes `{ payload P, a TEE attestation over it, the binding scheme,
//! the pinned enclave measurement }` and mints an [`AttestedFact`] ONLY when every
//! check passes:
//!
//! 1. **vendor crypto** — the injected [`TeeAttestationVerifier`] proves the report is a
//!    genuine, vendor-cert-chain-verified quote and yields [`TeeReportClaims`] (Nitro:
//!    COSE_Sign1 + X.509 chain to the pinned AWS root; SNP: VCEK←ASK←ARK + body ECDSA).
//!    Any authentication failure → [`AttestedError::Attestation`].
//! 2. **enclave identity** — `claims.measurement` must equal the pinned
//!    `expected_measurement` (the named published function / binary). A quote from a
//!    *different* binary → [`AttestedError::Measurement`].
//! 3. **payload binding** — `binding.commit(P)` must equal the attestation's
//!    `report_data`. So the fact is *this enclave bound THIS payload*, not a replayed or
//!    swapped one. A tampered / wrong payload → [`AttestedError::Unbound`].
//! 4. **TCB policy** — `claims.tcb_ok` (SNP down-level microcode fails; Nitro trust is a
//!    valid chain, always `true`). A down-level TCB → [`AttestedError::TcbBelowPolicy`].
//!
//! The result is checkable offline by anyone holding the attestation bytes and the
//! pinned root — no live server, no trusted feed operator.
//!
//! ## The honest grade: ATTESTED, not PROVED
//!
//! An [`AttestedFact`] carries [`TrustGrade::Attested`]. You still trust:
//!
//! - **the HW vendor's attestation root** (AWS Nitro G1 / AMD ARK) — not trustless;
//! - **the side-channel residual** — a genuine enclave can still leak via timing / power
//!   / speculative channels; attestation proves *code identity + binding*, not that the
//!   measured code is side-channel-free;
//! - **freshness** — a captured attestation is replayable unless a fresh nonce is folded
//!   into the payload commitment (bind `nonce ‖ price` and check the nonce upstream).
//!
//! That is why it is graded ATTESTED and never PROVED: PROVED is a machine-checked
//! theorem about the deployed artifact (e.g. the splitter-conservation money-path); this
//! is a hardware-rooted attestation about an input. The whole dreggfi pitch is that the
//! grade travels *with* the fact.
//!
//! ## Feeding the OCIP oracle-integrity leg (the money-path tie)
//!
//! This is the **input-integrity half** of the dreggfi weld. The other half is the
//! **money-path** — OCIP's revenue splitter (per-asset conservation) and fee router
//! ("exactly once"), which are **PROVED**: machine-checked conservation theorems over the
//! deployed clearing (`metatheory/Market/Clearing.lean::clearing_conserves_per_asset`,
//! lifting `Intent/Ring.lean::settleRing_conserves` / `settle_conserves` — per-asset
//! `Σ in = Σ out`). Those theorems clear value *against a mark*; they are **conditional on
//! the mark being correct**. The mark is exogenous — the theorem cannot prove the price.
//!
//! The composition is exactly:
//!
//! ```text
//!   AttestedFact { payload = price/mark, grade = ATTESTED }        ← this lane (input)
//!            │  the graded feed value the router/splitter clears against
//!            ▼
//!   settleRing / clearing (grade = PROVED: per-asset conservation)  ← the money-path
//! ```
//!
//! An [`AttestedFact`] is that graded feed value: the enclave-measured price/mark, bound
//! and offline-checkable. It carries its own grade into the settlement, so the composite
//! product is honestly graded at its **weakest leg** — a solvency/settlement claim that
//! consumes an ATTESTED mark is itself ATTESTED for the input, PROVED for the arithmetic,
//! never uniformly "PROVED". The residual named in `docs/deos/DREGGFI-VISION.md` §7–§8:
//! oracle inputs stay ATTESTED (HW-vendor trust + side-channel) until the price is *itself*
//! a ZK witness — the day the mark moves from ATTESTED to PROVED. That weld is future work;
//! this lane delivers the ATTESTED rung it composes on.

use dregg_cell::tee_attest::{TeeAttestationVerifier, TeeQuoteKind, TeeReportClaims};
use sha2::{Digest, Sha256};

/// Domain-separation tag for the [`PayloadBinding::Sha256`] commitment, so an
/// attested-data commitment can never collide with a commitment computed for another
/// dregg protocol over the same bytes.
pub const ATTESTED_DATA_DOMAIN: &[u8] = b"dregg-attested-data-v1";

/// The OCIP trust-grade spine. This lane mints exactly one grade — [`Attested`]
/// (hardware-rooted). PROVED (a machine-checked theorem about the deployed artifact) and
/// REPLAYABLE (a re-runnable ranking) are minted by other lanes; naming them here keeps
/// the grade an explicit, non-defaultable field of every fact.
///
/// [`Attested`]: TrustGrade::Attested
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TrustGrade {
    /// A hardware-rooted TEE attestation (SEV-SNP / TDX / Nitro) or zkTLS provenance:
    /// the data came from a named origin / named enclave. You trust the HW vendor root +
    /// the side-channel residual — which is *why* it is not `Proved`.
    Attested,
}

/// How the payload `P` is bound into the attestation's 32-byte `report_data` commitment.
/// The enclave computed `report_data = binding.commit(P)` at quote time; the verifier
/// recomputes it and requires equality.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PayloadBinding {
    /// `report_data = SHA-256(ATTESTED_DATA_DOMAIN ‖ P)`. The production mode for an
    /// arbitrary-length payload — a price string, a serialized mark, a security-flag
    /// record. The enclave hashes the data it produced into the quote.
    Sha256,
    /// `report_data = P`, with `P` exactly 32 bytes: the enclave bound the 32-byte
    /// commitment (a digest / Merkle root it already computed) directly. Use when the
    /// payload *is* the commitment the enclave measured.
    Raw32,
}

impl PayloadBinding {
    /// Compute the 32-byte commitment this binding expects in `report_data`.
    /// `Raw32` requires a 32-byte payload; `Sha256` accepts any length.
    pub fn commit(&self, payload: &[u8]) -> Result<[u8; 32], String> {
        match self {
            PayloadBinding::Sha256 => {
                let mut h = Sha256::new();
                h.update(ATTESTED_DATA_DOMAIN);
                h.update(payload);
                Ok(h.finalize().into())
            }
            PayloadBinding::Raw32 => {
                if payload.len() != 32 {
                    return Err(format!(
                        "Raw32 binding requires a 32-byte payload (the commitment itself), got {}",
                        payload.len()
                    ));
                }
                let mut c = [0u8; 32];
                c.copy_from_slice(payload);
                Ok(c)
            }
        }
    }
}

/// The request: a data payload carried with a TEE attestation over it, plus the pinned
/// enclave identity the attestation must match.
pub struct AttestedDataInput<'a> {
    /// Which TEE produced the attestation (dispatches the injected verifier's arm).
    pub kind: TeeQuoteKind,
    /// The raw vendor attestation bytes (Nitro COSE doc / `report(1184) ‖ vcek_der`).
    pub attestation: &'a [u8],
    /// The data payload the enclave produced / measured (a price, a mark, a flag record,
    /// or a 32-byte digest for `Raw32`).
    pub payload: &'a [u8],
    /// How `payload` is bound into the attestation's `report_data`.
    pub binding: PayloadBinding,
    /// The pinned code identity of the enclave that is *allowed* to produce this feed
    /// (the "named published function"). A quote from any other binary is refused.
    pub expected_measurement: [u8; 32],
}

/// An offline-checkable, ATTESTED-graded data fact: *enclave `E` (code identity
/// `measurement`) produced / measured `payload`, bound as `report_data`*.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AttestedFact {
    /// The TEE that produced the attestation.
    pub kind: TeeQuoteKind,
    /// The enclave's measured code identity (matches the pinned `expected_measurement`).
    pub measurement: [u8; 32],
    /// The data the fact is about (a graded feed value: price / mark / flag).
    pub payload: Vec<u8>,
    /// The commitment the enclave bound (`= binding.commit(payload) = claims.report_data`).
    pub report_data: [u8; 32],
    /// Whether the report's TCB met the verifier's pinned-minimum policy.
    pub tcb_ok: bool,
    /// The trust grade this fact carries — always [`TrustGrade::Attested`].
    pub grade: TrustGrade,
}

/// Why the lane refused to mint a fact (fail-closed — a fact is yielded ONLY when the
/// vendor crypto verified, the enclave matched, the payload was bound, and the TCB passed).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AttestedError {
    /// The vendor crypto refused the attestation (forged / tampered / bad chain /
    /// unknown kind / no pinned roots). Carries the verifier's message.
    Attestation(String),
    /// A genuine quote, but for a *different* measured binary than the pinned enclave.
    Measurement,
    /// A genuine quote, but its `report_data` is not the commitment to this payload —
    /// the payload was swapped, tampered, or the quote was replayed for other data.
    Unbound,
    /// A genuine quote from a TEE whose TCB (microcode/firmware) is below the pinned
    /// minimum policy.
    TcbBelowPolicy,
}

impl core::fmt::Display for AttestedError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            AttestedError::Attestation(e) => write!(f, "attestation refused by vendor crypto: {e}"),
            AttestedError::Measurement => {
                write!(f, "quote is for a different binary than the pinned enclave")
            }
            AttestedError::Unbound => write!(
                f,
                "report_data is not the commitment to this payload (swapped/tampered/replayed)"
            ),
            AttestedError::TcbBelowPolicy => write!(f, "TEE TCB below the pinned-minimum policy"),
        }
    }
}

impl std::error::Error for AttestedError {}

/// **THE ATTESTED-DATA LANE.** Verify a TEE attestation over `input.payload` and mint an
/// [`AttestedFact`] — or refuse, fail-closed. `verifier` is any installed
/// [`TeeAttestationVerifier`] (the real [`NitroVerifier`](crate::NitroVerifier) /
/// [`SnpVerifier`](crate::SnpVerifier), or the dispatching `TeeFactVerifier`).
///
/// See the module docs for the four ordered checks and the honest ATTESTED grade.
pub fn attest_data<V: TeeAttestationVerifier + ?Sized>(
    verifier: &V,
    input: &AttestedDataInput<'_>,
) -> Result<AttestedFact, AttestedError> {
    // 1. Vendor crypto: prove the report authentic and extract the claims.
    let claims: TeeReportClaims = verifier
        .verify_report(input.kind, input.attestation)
        .map_err(AttestedError::Attestation)?;

    // 2. Enclave identity: the quote must be for the pinned published function/binary.
    if claims.measurement != input.expected_measurement {
        return Err(AttestedError::Measurement);
    }

    // 3. Payload binding: report_data must be the commitment to THIS payload.
    let commitment = input
        .binding
        .commit(input.payload)
        .map_err(AttestedError::Attestation)?;
    if commitment != claims.report_data {
        return Err(AttestedError::Unbound);
    }

    // 4. TCB policy.
    if !claims.tcb_ok {
        return Err(AttestedError::TcbBelowPolicy);
    }

    Ok(AttestedFact {
        kind: input.kind,
        measurement: claims.measurement,
        payload: input.payload.to_vec(),
        report_data: claims.report_data,
        tcb_ok: claims.tcb_ok,
        grade: TrustGrade::Attested,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    // A test double for the injected vendor verifier: returns fixed claims for any report
    // so the lane's binding/measurement/tcb logic is exercised without real crypto. The
    // REAL vendor-crypto path is proven end-to-end by `tests/attested_data_lane.rs` against
    // the genuine captured AWS Nitro fixture.
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
    struct RejectTee;
    impl TeeAttestationVerifier for RejectTee {
        fn verify_report(&self, _k: TeeQuoteKind, _r: &[u8]) -> Result<TeeReportClaims, String> {
            Err("bad vendor signature".into())
        }
    }

    const MEAS: [u8; 32] = [7u8; 32];

    fn mock_over(payload: &[u8], binding: PayloadBinding, tcb_ok: bool) -> MockTee {
        MockTee(TeeReportClaims {
            measurement: MEAS,
            report_data: binding.commit(payload).unwrap(),
            tcb_ok,
        })
    }

    #[test]
    fn sha256_binding_over_a_price_payload_mints_the_fact() {
        // A realistic variable-length feed value.
        let price = br#"{"sym":"BTC-USD","px":"65012.50","t":1700000000}"#;
        let v = mock_over(price, PayloadBinding::Sha256, true);
        let fact = attest_data(
            &v,
            &AttestedDataInput {
                kind: TeeQuoteKind::SevSnp,
                attestation: b"opaque-report-bytes",
                payload: price,
                binding: PayloadBinding::Sha256,
                expected_measurement: MEAS,
            },
        )
        .expect("a genuine quote binding this price mints an ATTESTED fact");
        assert_eq!(fact.grade, TrustGrade::Attested);
        assert_eq!(fact.payload, price);
        assert_eq!(
            fact.report_data,
            PayloadBinding::Sha256.commit(price).unwrap()
        );
    }

    #[test]
    fn tampered_payload_is_unbound_and_refused() {
        // The quote bound the honest price; a splicer presents a DIFFERENT price with the
        // same attestation → the recomputed commitment disagrees with report_data.
        let honest = br#"{"sym":"BTC-USD","px":"65012.50"}"#;
        let tampered = br#"{"sym":"BTC-USD","px":"99999.99"}"#;
        let v = mock_over(honest, PayloadBinding::Sha256, true);
        let err = attest_data(
            &v,
            &AttestedDataInput {
                kind: TeeQuoteKind::SevSnp,
                attestation: b"opaque",
                payload: tampered,
                binding: PayloadBinding::Sha256,
                expected_measurement: MEAS,
            },
        )
        .unwrap_err();
        assert_eq!(err, AttestedError::Unbound);
    }

    #[test]
    fn wrong_enclave_measurement_is_refused() {
        let payload = b"security-flag:LISTED";
        let v = mock_over(payload, PayloadBinding::Sha256, true);
        let err = attest_data(
            &v,
            &AttestedDataInput {
                kind: TeeQuoteKind::SevSnp,
                attestation: b"opaque",
                payload,
                binding: PayloadBinding::Sha256,
                expected_measurement: [0xEEu8; 32], // not MEAS
            },
        )
        .unwrap_err();
        assert_eq!(err, AttestedError::Measurement);
    }

    #[test]
    fn forged_attestation_is_refused() {
        let err = attest_data(
            &RejectTee,
            &AttestedDataInput {
                kind: TeeQuoteKind::SevSnp,
                attestation: b"forged",
                payload: b"anything",
                binding: PayloadBinding::Sha256,
                expected_measurement: MEAS,
            },
        )
        .unwrap_err();
        assert!(matches!(err, AttestedError::Attestation(_)));
    }

    #[test]
    fn down_level_tcb_is_refused() {
        let payload = b"mark:AAPL:230.10";
        let v = mock_over(payload, PayloadBinding::Sha256, false);
        let err = attest_data(
            &v,
            &AttestedDataInput {
                kind: TeeQuoteKind::SevSnp,
                attestation: b"opaque",
                payload,
                binding: PayloadBinding::Sha256,
                expected_measurement: MEAS,
            },
        )
        .unwrap_err();
        assert_eq!(err, AttestedError::TcbBelowPolicy);
    }

    #[test]
    fn raw32_binding_requires_and_binds_a_32_byte_commitment() {
        let digest = [0xABu8; 32];
        let v = mock_over(&digest, PayloadBinding::Raw32, true);
        let fact = attest_data(
            &v,
            &AttestedDataInput {
                kind: TeeQuoteKind::AwsNitro,
                attestation: b"opaque",
                payload: &digest,
                binding: PayloadBinding::Raw32,
                expected_measurement: MEAS,
            },
        )
        .expect("a 32-byte Raw32 commitment binds");
        assert_eq!(fact.report_data, digest);

        // A non-32-byte payload under Raw32 is a binding error (surfaced as Attestation).
        assert!(PayloadBinding::Raw32.commit(b"short").is_err());
    }

    #[test]
    fn sha256_and_raw32_are_domain_separated() {
        // The Sha256 commitment folds the domain tag, so it never equals a 32-byte
        // payload's Raw32 identity commitment for the same bytes.
        let bytes = [0x11u8; 32];
        assert_ne!(
            PayloadBinding::Sha256.commit(&bytes).unwrap(),
            PayloadBinding::Raw32.commit(&bytes).unwrap()
        );
    }
}
