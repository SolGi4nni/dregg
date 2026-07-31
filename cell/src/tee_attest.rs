//! TEE attestation as a dregg-verifiable fact — the confidential-execution primitive.
//!
//! A hardware TEE (AMD SEV-SNP, Intel TDX/SGX, AWS Nitro) can produce a **remote
//! attestation quote**: a vendor-signed statement that a *specific measured binary*
//! is running inside a *genuine enclave*, carrying 64 bytes of caller-chosen
//! `report_data`. This module turns that quote into a first-class dregg fact on the
//! **same rail** the zkTLS/DECO oracle facts already ride — a
//! [`WitnessedPredicateKind::Custom`] verifier whose commitment a light client
//! re-checks against the landed [`grain_turn::ATTESTATION_SLOT`]. So an
//! enclave-attested grain turn becomes a receipt the owner (or any light client)
//! verifies: *the host ran binary M inside a real TEE, over this exact turn/session.*
//!
//! ## What it proves, and the honest boundary
//!
//! Accepting a TEE fact proves **code-integrity + confidentiality from a single
//! machine, with no quorum and no determinism requirement** — the one guarantee the
//! determinism-bound consensus quorum structurally cannot give a *non-deterministic*
//! agent-loop (you cannot quorum-re-execute an LLM turn for identical output). It does
//! NOT prove the LLM's *output* is correct, and it is **single-hardware-root, not
//! trustless**: you trust the CPU vendor's attestation root + accept side-channel,
//! freshness (bind a nonce into `report_data`), and TCB-recovery caveats. Name it
//! "single-hardware-root execution-integrity."
//!
//! ## Layering (the same discipline as the STARK verifiers)
//!
//! `dregg-cell` must stay light — it does NOT link the vendor crypto (AMD KDS cert
//! chains, P-384 ECDSA, DCAP quote parsing). So this module holds only the *shape*:
//! the [`TeeAttestationVerifier`] trait (the injected crypto seam) and a fail-closed
//! [`TeeWitnessedPredicateVerifier`] that rejects every proof until a real verifier is
//! installed by the host (mirrors [`crate::predicate::NotYetWiredVerifier`] and the
//! neighbor-adjacency STARK injection). The real SEV-SNP / DCAP verifier — parsing the
//! report, verifying the vendor cert chain to the AMD/Intel root, and extracting the
//! [`TeeReportClaims`] — lives host-side and installs via
//! [`crate::predicate::WitnessedPredicateRegistry::register_custom`] under
//! [`tee_predicate_vk`].

use std::sync::Arc;

use crate::predicate::{
    InputRef, PredicateInput, WitnessedPredicate, WitnessedPredicateError, WitnessedPredicateKind,
    WitnessedPredicateVerifier, canonical_predicate_vk,
};

/// Which TEE produced the quote. Encoded as the FIRST byte of the proof blob so one
/// registered verifier can dispatch to the right vendor path.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum TeeQuoteKind {
    /// AMD SEV-SNP confidential VM (whole-VM; the recommended first target — the grain
    /// image runs unmodified). Report verified against the AMD KDS (VCEK → ASK → ARK).
    SevSnp = 1,
    /// Intel TDX trust domain (the TDX-equivalent of SNP; same "verify a CVM quote" shape).
    IntelTdx = 2,
    /// Intel SGX enclave (process-enclave; heavier porting — DCAP quote).
    IntelSgx = 3,
    /// AWS Nitro Enclave (NSM COSE-signed attestation doc, AWS root).
    AwsNitro = 4,
}

impl TeeQuoteKind {
    /// Decode the leading dispatch byte.
    pub fn from_u8(b: u8) -> Option<TeeQuoteKind> {
        match b {
            1 => Some(TeeQuoteKind::SevSnp),
            2 => Some(TeeQuoteKind::IntelTdx),
            3 => Some(TeeQuoteKind::IntelSgx),
            4 => Some(TeeQuoteKind::AwsNitro),
            _ => None,
        }
    }
}

/// **What a TCB policy decided about a report — including "nothing did".**
///
/// ⚑ MEASURED 2026-07-30. This used to be a bare `tcb_ok: bool`, and
/// `tee_verify::verify_nitro_core` set it to a hardcoded `true` for every AWS Nitro
/// attestation document, with the reason in a trailing comment. A caller reading
/// `claims.tcb_ok` — including the fail-closed `attested_data` gate, whose whole job is
/// to refuse a down-level TCB — was told a policy had passed when no policy had run. A
/// disclosure in a comment is not a value a caller can branch on; this enum is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TcbStatus {
    /// A TCB policy RAN and this report met it (SNP: `REPORTED_TCB` at or above the pinned
    /// minimum; TDX: the quote's DCAP status is in the verifier's accepted set).
    MetPolicy,
    /// A TCB policy RAN and this report is BELOW it — a genuine quote from a down-level
    /// (potentially vulnerable) TCB. Refused.
    BelowPolicy,
    /// ⚑ **NO POLICY RAN**, because this platform's attestation carries no TCB rung to gate
    /// on. AWS Nitro is the case: its trust is a valid certificate chain to the pinned root
    /// plus the PCR measurement, and the document exposes no microcode/firmware version a
    /// minimum could be compared against. This is **not a pass**. A caller that needs a TCB
    /// decision must treat it as an absent one and decide explicitly — see
    /// `tee_verify::attested_data`, which admits it only because the enclave-identity pin
    /// (`expected_measurement`) is doing the whole job on that platform, and says so.
    NoPolicyOnPlatform,
}

impl TcbStatus {
    /// Whether a fail-closed gate must REFUSE on this status. Only [`TcbStatus::BelowPolicy`]
    /// is a refusal: a platform with no TCB rung cannot fail one. Deliberately NOT named
    /// `is_ok` — there is no arm of this enum that means "a TCB policy vouched for this
    /// report" *and* is reachable on every platform, which is exactly the fact the old
    /// boolean erased.
    pub fn is_refusal(self) -> bool {
        matches!(self, TcbStatus::BelowPolicy)
    }

    /// The stable machine-readable token, for a surface that reports what it checked.
    pub fn token(self) -> &'static str {
        match self {
            TcbStatus::MetPolicy => "met-pinned-minimum",
            TcbStatus::BelowPolicy => "below-pinned-minimum",
            TcbStatus::NoPolicyOnPlatform => "no-tcb-rung-on-this-platform",
        }
    }
}

/// The claims a genuine, vendor-cert-chain-verified TEE report yields. The injected
/// [`TeeAttestationVerifier`] is responsible for having proven the report authentic
/// (vendor signature + cert chain to the hardware root) BEFORE returning these — a
/// verifier that returns claims from an unverified report is a soundness bug.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TeeReportClaims {
    /// The measured code identity (SNP launch measurement / TDX MRTD / SGX MRENCLAVE /
    /// Nitro PCRs folded). Compared against the predicate's pinned expected measurement.
    pub measurement: [u8; 32],
    /// The 32 bytes the enclave bound into the quote's `report_data` — MUST equal the
    /// turn/session commitment the predicate's input points at, or the quote is stale
    /// (replayed) or unbound.
    pub report_data: [u8; 32],
    /// What a TCB policy decided — **or that none ran**. See [`TcbStatus`]; the old
    /// `tcb_ok: bool` is GONE so every consumer breaks loudly rather than reading a
    /// hardcoded `true` as a check that happened.
    pub tcb: TcbStatus,
}

/// The injected crypto seam. The host installs a real implementation (SEV-SNP / DCAP /
/// Nitro) that verifies the report's vendor signature + cert chain to the hardware root
/// and extracts [`TeeReportClaims`]. `dregg-cell` ships NO implementation — until one is
/// installed the [`TeeWitnessedPredicateVerifier`] fails closed.
pub trait TeeAttestationVerifier: Send + Sync {
    /// Verify `report_bytes` as a genuine `kind` attestation (vendor signature + cert
    /// chain to the hardware root) and extract its claims. `Err` on any failure — an
    /// implementation MUST NOT return `Ok` for an unauthenticated report.
    fn verify_report(
        &self,
        kind: TeeQuoteKind,
        report_bytes: &[u8],
    ) -> Result<TeeReportClaims, String>;
}

/// Encode a TEE proof blob for the witness: `[kind_byte][raw vendor report bytes]`.
pub fn encode_tee_proof(kind: TeeQuoteKind, report_bytes: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(1 + report_bytes.len());
    out.push(kind as u8);
    out.extend_from_slice(report_bytes);
    out
}

/// The canonical `vk_hash` for the TEE-attestation predicate. Stable identifier a host
/// registers its real verifier under, and the value pinned in
/// [`WitnessedPredicateKind::Custom`] for every TEE fact.
pub fn tee_predicate_vk() -> [u8; 32] {
    canonical_predicate_vk(b"dregg-tee-attestation-verifier-v1")
}

/// Build the [`WitnessedPredicate`] for "this turn ran inside a genuine TEE running the
/// binary measured as `expected_measurement`, bound to the commitment in state slot
/// `report_data_slot`." The verifier reads the bound commitment from that cell slot and
/// requires the quote's `report_data` to equal it.
pub fn tee_attestation_predicate(
    expected_measurement: [u8; 32],
    report_data_slot: u8,
) -> WitnessedPredicate {
    WitnessedPredicate {
        kind: WitnessedPredicateKind::Custom {
            vk_hash: tee_predicate_vk(),
        },
        commitment: expected_measurement,
        input_ref: InputRef::Slot {
            index: report_data_slot,
        },
        // The report blob rides witness index 0 of the action.
        proof_witness_index: 0,
    }
}

/// The [`WitnessedPredicateVerifier`] for TEE attestation. Fail-closed: constructed
/// with no injected [`TeeAttestationVerifier`] it rejects every proof; the host installs
/// the real vendor verifier with [`Self::with_verifier`].
pub struct TeeWitnessedPredicateVerifier {
    inner: Option<Arc<dyn TeeAttestationVerifier>>,
}

impl TeeWitnessedPredicateVerifier {
    /// A fail-closed verifier (no vendor crypto installed — rejects everything).
    pub fn new() -> TeeWitnessedPredicateVerifier {
        TeeWitnessedPredicateVerifier { inner: None }
    }

    /// Install the real vendor-report verifier (SEV-SNP / DCAP / Nitro), host-side.
    pub fn with_verifier(
        verifier: Arc<dyn TeeAttestationVerifier>,
    ) -> TeeWitnessedPredicateVerifier {
        TeeWitnessedPredicateVerifier {
            inner: Some(verifier),
        }
    }
}

impl Default for TeeWitnessedPredicateVerifier {
    fn default() -> Self {
        Self::new()
    }
}

/// Read the predicate input as a 32-byte commitment (the bound `report_data` target).
fn input_commitment(input: &PredicateInput<'_>) -> Result<[u8; 32], WitnessedPredicateError> {
    match input {
        PredicateInput::Slot(s) => Ok(**s),
        PredicateInput::Bytes(b) if b.len() == 32 => {
            let mut c = [0u8; 32];
            c.copy_from_slice(b);
            Ok(c)
        }
        _ => Err(WitnessedPredicateError::InputShapeMismatch {
            kind_name: "tee-attestation",
            expected: "a 32-byte report_data commitment (Slot or 32-byte Bytes)",
            actual: "a non-32-byte or non-slot input",
        }),
    }
}

impl WitnessedPredicateVerifier for TeeWitnessedPredicateVerifier {
    fn name(&self) -> &'static str {
        "tee-attestation"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::Custom {
            vk_hash: tee_predicate_vk(),
        }
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        // FAIL-CLOSED: no vendor verifier installed => reject (mirrors the STARK
        // neighbor-adjacency default). A cluster that has not wired a TEE verifier
        // cannot be tricked into accepting an unverified quote.
        let inner = self
            .inner
            .as_ref()
            .ok_or_else(|| WitnessedPredicateError::Rejected {
                kind_name: "tee-attestation",
                reason: "no TeeAttestationVerifier installed (fail-closed)".to_string(),
            })?;

        // proof = [kind_byte][vendor report].
        let (kind_byte, report) =
            proof_bytes
                .split_first()
                .ok_or_else(|| WitnessedPredicateError::Rejected {
                    kind_name: "tee-attestation",
                    reason: "empty TEE proof blob".to_string(),
                })?;
        let kind =
            TeeQuoteKind::from_u8(*kind_byte).ok_or_else(|| WitnessedPredicateError::Rejected {
                kind_name: "tee-attestation",
                reason: format!("unknown TEE quote kind {kind_byte}"),
            })?;

        // The injected verifier proves the report is a GENUINE vendor-signed quote and
        // extracts its claims. Any authentication failure surfaces here as Rejected.
        let claims =
            inner
                .verify_report(kind, report)
                .map_err(|e| WitnessedPredicateError::Rejected {
                    kind_name: "tee-attestation",
                    reason: format!("TEE report verification failed: {e}"),
                })?;

        // The pinned expected code identity: the predicate commitment IS the expected
        // measurement. A quote for a different binary is refused.
        if &claims.measurement != commitment {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: "tee-attestation",
                reason: "measurement does not match the pinned expected binary".to_string(),
            });
        }

        // Freshness / binding: the quote's report_data must equal the turn/session
        // commitment the input points at, or the quote is unbound or replayed.
        let expected_report_data = input_commitment(input)?;
        if claims.report_data != expected_report_data {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: "tee-attestation",
                reason: "report_data is not bound to the committed turn/session".to_string(),
            });
        }

        // ⚑ ONLY `BelowPolicy` refuses. `NoPolicyOnPlatform` (AWS Nitro, which exposes no
        // TCB rung) is admitted on the strength of the measurement pin checked above and
        // the vendor chain the verifier already proved — NOT because a TCB policy passed.
        // The old `if !claims.tcb_ok` could never fire for Nitro because the verifier
        // hardcoded `true`; the distinction is now in the type instead of in a comment.
        if claims.tcb.is_refusal() {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: "tee-attestation",
                reason: format!("TEE TCB policy: {}", claims.tcb.token()),
            });
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const M: [u8; 32] = [7u8; 32];
    const RD: [u8; 32] = [9u8; 32];

    /// A test double for the injected vendor verifier — returns fixed claims for any
    /// report so the binding/measurement/tcb logic can be exercised without real crypto.
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
    /// A test double that fails authentication (an unverifiable/forged report).
    struct RejectTee;
    impl TeeAttestationVerifier for RejectTee {
        fn verify_report(&self, _k: TeeQuoteKind, _r: &[u8]) -> Result<TeeReportClaims, String> {
            Err("bad vendor signature".to_string())
        }
    }

    fn proof() -> Vec<u8> {
        encode_tee_proof(TeeQuoteKind::SevSnp, b"snp-report-bytes")
    }

    #[test]
    fn no_verifier_installed_fails_closed() {
        let v = TeeWitnessedPredicateVerifier::new();
        let err = v
            .verify(&M, &PredicateInput::Slot(&RD), &proof())
            .unwrap_err();
        assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
    }

    #[test]
    fn matching_measurement_and_report_data_accept() {
        let v = TeeWitnessedPredicateVerifier::with_verifier(Arc::new(MockTee(TeeReportClaims {
            measurement: M,
            report_data: RD,
            tcb: TcbStatus::MetPolicy,
        })));
        assert!(v.verify(&M, &PredicateInput::Slot(&RD), &proof()).is_ok());
    }

    #[test]
    fn wrong_measurement_rejected() {
        let v = TeeWitnessedPredicateVerifier::with_verifier(Arc::new(MockTee(TeeReportClaims {
            measurement: [1u8; 32], // not M
            report_data: RD,
            tcb: TcbStatus::MetPolicy,
        })));
        assert!(v.verify(&M, &PredicateInput::Slot(&RD), &proof()).is_err());
    }

    #[test]
    fn wrong_report_data_rejected() {
        let v = TeeWitnessedPredicateVerifier::with_verifier(Arc::new(MockTee(TeeReportClaims {
            measurement: M,
            report_data: [2u8; 32], // not the committed RD
            tcb: TcbStatus::MetPolicy,
        })));
        // input pins RD, but the quote bound something else -> replayed/unbound.
        assert!(v.verify(&M, &PredicateInput::Slot(&RD), &proof()).is_err());
    }

    #[test]
    fn down_level_tcb_rejected() {
        let v = TeeWitnessedPredicateVerifier::with_verifier(Arc::new(MockTee(TeeReportClaims {
            measurement: M,
            report_data: RD,
            tcb: TcbStatus::BelowPolicy,
        })));
        assert!(v.verify(&M, &PredicateInput::Slot(&RD), &proof()).is_err());
    }

    /// ⚑ **A PLATFORM WITH NO TCB RUNG IS ADMITTED, AND THE REFUSAL SAYS WHICH ARM FIRED.**
    ///
    /// The two facts this pins, which the old `tcb_ok: bool` could not express:
    /// `NoPolicyOnPlatform` is NOT a refusal (Nitro would otherwise be unusable), and it is
    /// NOT `MetPolicy` either — a caller can tell them apart, which is the whole point of
    /// the migration. Before this, `tee_verify::verify_nitro_core` hardcoded `tcb_ok: true`
    /// and every reader was told a policy had passed.
    #[test]
    fn a_platform_with_no_tcb_rung_is_admitted_but_never_reported_as_a_policy_pass() {
        let v = TeeWitnessedPredicateVerifier::with_verifier(Arc::new(MockTee(TeeReportClaims {
            measurement: M,
            report_data: RD,
            tcb: TcbStatus::NoPolicyOnPlatform,
        })));
        assert!(
            v.verify(&M, &PredicateInput::Slot(&RD), &proof()).is_ok(),
            "a platform that carries no TCB rung cannot fail a TCB policy, so the gate must \
             not refuse it — the measurement pin is what is doing the work there"
        );
        assert_ne!(
            TcbStatus::NoPolicyOnPlatform,
            TcbStatus::MetPolicy,
            "the two must be DISTINGUISHABLE by a caller; collapsing them back to one \
             boolean is exactly the defect this enum replaced"
        );
        assert!(!TcbStatus::NoPolicyOnPlatform.is_refusal());
        assert!(TcbStatus::BelowPolicy.is_refusal());
        assert_eq!(
            TcbStatus::NoPolicyOnPlatform.token(),
            "no-tcb-rung-on-this-platform",
            "a surface reporting what it checked must be able to print the absence"
        );
    }

    #[test]
    fn forged_report_rejected() {
        let v = TeeWitnessedPredicateVerifier::with_verifier(Arc::new(RejectTee));
        assert!(v.verify(&M, &PredicateInput::Slot(&RD), &proof()).is_err());
    }

    #[test]
    fn empty_proof_rejected() {
        let v = TeeWitnessedPredicateVerifier::with_verifier(Arc::new(MockTee(TeeReportClaims {
            measurement: M,
            report_data: RD,
            tcb: TcbStatus::MetPolicy,
        })));
        assert!(v.verify(&M, &PredicateInput::Slot(&RD), &[]).is_err());
    }

    #[test]
    fn kind_matches_registered_vk() {
        let v = TeeWitnessedPredicateVerifier::new();
        assert_eq!(
            v.kind(),
            WitnessedPredicateKind::Custom {
                vk_hash: tee_predicate_vk()
            }
        );
    }

    #[test]
    fn predicate_builder_pins_measurement_and_slot() {
        let p = tee_attestation_predicate(M, 8);
        assert_eq!(p.commitment, M);
        assert!(matches!(p.input_ref, InputRef::Slot { index: 8 }));
        assert!(matches!(p.kind, WitnessedPredicateKind::Custom { .. }));
    }
}
