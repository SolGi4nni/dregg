//! Canonical quorum attestations for one-bit party-MPC decision circuits.
//!
//! [`crate::mpc_party::DistributedDecisionRun`] is deliberately an in-process,
//! non-cloneable capability.  This module supplies the durable public companion:
//! a strict claim over the candidate/session nonce, exact equality-circuit
//! parameters, reveal-only transcript digest, and the one released bit.
//!
//! A threshold Ed25519 endorsement authenticates that the configured roster
//! agreed on this exact claim.  It does **not** prove that malicious parties
//! derived their arithmetic shares from the claimed BFV ciphertext.  That
//! same-opening/input-validity proof remains a separate protocol obligation.
//! Equality (`FHDAR001`) and strict comparison (`FHCAR001`) use disjoint claim,
//! transcript, wire, and replay domains so their bits cannot cross-authorize.

use std::fmt;

use sha2::{Digest, Sha256};

use crate::attestation::{
    ComputationIntegrityEvidence, ComputationIntegrityResidual, ComputationIntegrityVerifier,
    Digest32, ReplayGuard,
};
use crate::mpc_party::{ComparisonTranscript, DecisionTranscript, PartyMpcSession};

pub const DECISION_ATTESTATION_PROTOCOL_ID: [u8; 32] = *b"FHEGG-PRIVATE-DECISION-ATTEST-V1";
pub const COMPARISON_ATTESTATION_PROTOCOL_ID: [u8; 32] = *b"FHEGG-PRIVATE-COMPARE-ATTEST-V1!";

const CLAIM_DOMAIN: &[u8] = b"fhegg/decision-attestation/claim/v1";
const TRANSCRIPT_DOMAIN: &[u8] = b"fhegg/decision-attestation/transcript/v1";
const ENVELOPE_DOMAIN: &[u8] = b"fhegg/decision-attestation/envelope/v1";
const REPLAY_DOMAIN: &[u8] = b"fhegg/decision-attestation/replay/v1";
const COMPARISON_CLAIM_DOMAIN: &[u8] = b"fhegg/comparison-attestation/claim/v1";
const COMPARISON_TRANSCRIPT_DOMAIN: &[u8] = b"fhegg/comparison-attestation/transcript/v1";
const COMPARISON_ENVELOPE_DOMAIN: &[u8] = b"fhegg/comparison-attestation/envelope/v1";
const COMPARISON_REPLAY_DOMAIN: &[u8] = b"fhegg/comparison-attestation/replay/v1";
const WIRE_MAGIC: &[u8; 8] = b"FHDAR001";
const COMPARISON_WIRE_MAGIC: &[u8; 8] = b"FHCAR001";
const MAX_EVIDENCE_BYTES: usize = 1024 * 1024;

fn domain_digest(domain: &[u8], bytes: &[u8]) -> Digest32 {
    let mut hasher = Sha256::new();
    hasher.update((domain.len() as u64).to_be_bytes());
    hasher.update(domain);
    hasher.update((bytes.len() as u64).to_be_bytes());
    hasher.update(bytes);
    hasher.finalize().into()
}

#[derive(Default)]
struct CanonicalBytes(Vec<u8>);

impl CanonicalBytes {
    fn u8(&mut self, value: u8) {
        self.0.push(value);
    }

    fn u64(&mut self, value: u64) {
        self.0.extend_from_slice(&value.to_be_bytes());
    }

    fn digest(&mut self, value: &Digest32) {
        self.0.extend_from_slice(value);
    }

    fn finish(self) -> Vec<u8> {
        self.0
    }
}

/// Every public fact covered by the decision quorum signatures.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DecisionClaim {
    pub protocol_id: Digest32,
    /// Candidate/context-bound nonce. A process-local decision can use
    /// `PrivateAppliedSwap::decision_session_nonce()` directly; a hosted
    /// collective service uses the digest of its canonical decision task so
    /// the claim also binds the table session, sequence, committed material,
    /// and public collective identity.
    pub session_nonce: Digest32,
    pub roster_digest: Digest32,
    pub n_parties: u64,
    pub value_bits: u64,
    pub plaintext_modulus: u64,
    pub transcript_digest: Digest32,
    pub equal: bool,
}

impl DecisionClaim {
    fn canonical_bytes(&self) -> Vec<u8> {
        let mut out = CanonicalBytes::default();
        out.digest(&self.protocol_id);
        out.digest(&self.session_nonce);
        out.digest(&self.roster_digest);
        out.u64(self.n_parties);
        out.u64(self.value_bits);
        out.u64(self.plaintext_modulus);
        out.digest(&self.transcript_digest);
        out.u8(u8::from(self.equal));
        out.finish()
    }

    pub fn digest(&self) -> Digest32 {
        domain_digest(CLAIM_DOMAIN, &self.canonical_bytes())
    }
}

/// The expected public objects come from the relying party, never from the
/// receipt being checked.
pub struct ExpectedDecisionContext<'a> {
    pub session: &'a PartyMpcSession,
    pub roster_digest: Digest32,
    pub transcript: &'a DecisionTranscript,
    pub equal: bool,
}

/// Every public fact covered by a strict-comparison quorum signature.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComparisonClaim {
    pub protocol_id: Digest32,
    pub session_nonce: Digest32,
    pub roster_digest: Digest32,
    pub n_parties: u64,
    pub value_bits: u64,
    pub plaintext_modulus: u64,
    pub transcript_digest: Digest32,
    pub less_than: bool,
}

impl ComparisonClaim {
    fn canonical_bytes(&self) -> Vec<u8> {
        let mut out = CanonicalBytes::default();
        out.digest(&self.protocol_id);
        out.digest(&self.session_nonce);
        out.digest(&self.roster_digest);
        out.u64(self.n_parties);
        out.u64(self.value_bits);
        out.u64(self.plaintext_modulus);
        out.digest(&self.transcript_digest);
        out.u8(u8::from(self.less_than));
        out.finish()
    }

    pub fn digest(&self) -> Digest32 {
        domain_digest(COMPARISON_CLAIM_DOMAIN, &self.canonical_bytes())
    }
}

/// Independently reconstructed public objects for one comparison receipt.
pub struct ExpectedComparisonContext<'a> {
    pub session: &'a PartyMpcSession,
    pub roster_digest: Digest32,
    pub transcript: &'a ComparisonTranscript,
    pub less_than: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DecisionAttestationError {
    TranscriptNotRevealOnly,
    TranscriptOutputMismatch,
    BindingMismatch,
    ComputationIntegrityResidual(ComputationIntegrityResidual),
    IntegrityVerifierMismatch,
    InvalidComputationIntegrityEvidence,
    ReplayDetected,
    InvalidWire,
    EvidenceTooLarge,
}

impl fmt::Display for DecisionAttestationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "decision attestation error: {self:?}")
    }
}

impl std::error::Error for DecisionAttestationError {}

pub type Result<T> = std::result::Result<T, DecisionAttestationError>;

/// Durable public envelope for an equality decision.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttestedDecisionReceipt {
    pub claim: DecisionClaim,
    pub computation_integrity: ComputationIntegrityEvidence,
}

impl AttestedDecisionReceipt {
    pub fn issue(
        context: &ExpectedDecisionContext<'_>,
        computation_integrity: ComputationIntegrityEvidence,
    ) -> Result<Self> {
        Ok(Self {
            claim: claim_from_context(context)?,
            computation_integrity,
        })
    }

    pub fn claim_digest(&self) -> Digest32 {
        self.claim.digest()
    }

    /// Stable, strict transport bytes.  They contain no operand, residue,
    /// ciphertext, Beaver triple, or party share.
    pub fn to_wire_bytes(&self) -> Result<Vec<u8>> {
        let mut out = Vec::new();
        out.extend_from_slice(WIRE_MAGIC);
        out.extend_from_slice(&self.claim.canonical_bytes());
        match &self.computation_integrity {
            ComputationIntegrityEvidence::BindingOnly(
                ComputationIntegrityResidual::OutputOnlySelfAssertion,
            ) => {
                out.push(0);
            }
            ComputationIntegrityEvidence::External {
                verifier_id,
                evidence,
            } => {
                if evidence.len() > MAX_EVIDENCE_BYTES {
                    return Err(DecisionAttestationError::EvidenceTooLarge);
                }
                out.push(1);
                out.extend_from_slice(verifier_id);
                out.extend_from_slice(&(evidence.len() as u64).to_be_bytes());
                out.extend_from_slice(evidence);
            }
        }
        Ok(out)
    }

    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self> {
        let mut cursor = WireCursor { bytes, offset: 0 };
        if cursor.take(WIRE_MAGIC.len())? != WIRE_MAGIC {
            return Err(DecisionAttestationError::InvalidWire);
        }
        let claim = DecisionClaim {
            protocol_id: cursor.digest()?,
            session_nonce: cursor.digest()?,
            roster_digest: cursor.digest()?,
            n_parties: cursor.u64()?,
            value_bits: cursor.u64()?,
            plaintext_modulus: cursor.u64()?,
            transcript_digest: cursor.digest()?,
            equal: match cursor.u8()? {
                0 => false,
                1 => true,
                _ => return Err(DecisionAttestationError::InvalidWire),
            },
        };
        if claim.protocol_id != DECISION_ATTESTATION_PROTOCOL_ID {
            return Err(DecisionAttestationError::InvalidWire);
        }
        let computation_integrity = match cursor.u8()? {
            0 => ComputationIntegrityEvidence::BindingOnly(
                ComputationIntegrityResidual::OutputOnlySelfAssertion,
            ),
            1 => {
                let verifier_id = cursor.digest()?;
                let len = usize::try_from(cursor.u64()?)
                    .map_err(|_| DecisionAttestationError::InvalidWire)?;
                if len > MAX_EVIDENCE_BYTES {
                    return Err(DecisionAttestationError::EvidenceTooLarge);
                }
                ComputationIntegrityEvidence::External {
                    verifier_id,
                    evidence: cursor.take(len)?.to_vec(),
                }
            }
            _ => return Err(DecisionAttestationError::InvalidWire),
        };
        if cursor.offset != bytes.len() {
            return Err(DecisionAttestationError::InvalidWire);
        }
        Ok(Self {
            claim,
            computation_integrity,
        })
    }

    pub fn envelope_digest(&self) -> Result<Digest32> {
        Ok(domain_digest(ENVELOPE_DOMAIN, &self.to_wire_bytes()?))
    }

    pub fn verify_binding(&self, expected: &ExpectedDecisionContext<'_>) -> Result<()> {
        if self.claim != claim_from_context(expected)? {
            return Err(DecisionAttestationError::BindingMismatch);
        }
        Ok(())
    }

    /// Evidence is checked before the replay id is consumed.
    pub fn verify_full<V: ComputationIntegrityVerifier, R: ReplayGuard>(
        &self,
        expected: &ExpectedDecisionContext<'_>,
        verifier: &V,
        replay_guard: &mut R,
    ) -> Result<()> {
        self.verify_binding(expected)?;
        let (verifier_id, evidence) = match &self.computation_integrity {
            ComputationIntegrityEvidence::BindingOnly(residual) => {
                return Err(DecisionAttestationError::ComputationIntegrityResidual(
                    *residual,
                ));
            }
            ComputationIntegrityEvidence::External {
                verifier_id,
                evidence,
            } => (verifier_id, evidence),
        };
        if verifier_id != &verifier.verifier_id() {
            return Err(DecisionAttestationError::IntegrityVerifierMismatch);
        }
        if !verifier.verify(&self.claim.digest(), evidence) {
            return Err(DecisionAttestationError::InvalidComputationIntegrityEvidence);
        }
        if !replay_guard.check_and_record(self.replay_id()) {
            return Err(DecisionAttestationError::ReplayDetected);
        }
        Ok(())
    }

    fn replay_id(&self) -> Digest32 {
        let mut bytes = CanonicalBytes::default();
        bytes.digest(&self.claim.protocol_id);
        bytes.digest(&self.claim.session_nonce);
        bytes.digest(&self.claim.roster_digest);
        domain_digest(REPLAY_DOMAIN, &bytes.finish())
    }
}

/// Durable public envelope for a strict secret-shared comparison.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttestedComparisonReceipt {
    pub claim: ComparisonClaim,
    pub computation_integrity: ComputationIntegrityEvidence,
}

impl AttestedComparisonReceipt {
    pub fn issue(
        context: &ExpectedComparisonContext<'_>,
        computation_integrity: ComputationIntegrityEvidence,
    ) -> Result<Self> {
        Ok(Self {
            claim: comparison_claim_from_context(context)?,
            computation_integrity,
        })
    }

    pub fn claim_digest(&self) -> Digest32 {
        self.claim.digest()
    }

    /// Stable comparison receipt bytes. Operands, differences, residues,
    /// Beaver material, and party shares are absent.
    pub fn to_wire_bytes(&self) -> Result<Vec<u8>> {
        let mut out = Vec::new();
        out.extend_from_slice(COMPARISON_WIRE_MAGIC);
        out.extend_from_slice(&self.claim.canonical_bytes());
        match &self.computation_integrity {
            ComputationIntegrityEvidence::BindingOnly(
                ComputationIntegrityResidual::OutputOnlySelfAssertion,
            ) => out.push(0),
            ComputationIntegrityEvidence::External {
                verifier_id,
                evidence,
            } => {
                if evidence.len() > MAX_EVIDENCE_BYTES {
                    return Err(DecisionAttestationError::EvidenceTooLarge);
                }
                out.push(1);
                out.extend_from_slice(verifier_id);
                out.extend_from_slice(&(evidence.len() as u64).to_be_bytes());
                out.extend_from_slice(evidence);
            }
        }
        Ok(out)
    }

    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self> {
        let mut cursor = WireCursor { bytes, offset: 0 };
        if cursor.take(COMPARISON_WIRE_MAGIC.len())? != COMPARISON_WIRE_MAGIC {
            return Err(DecisionAttestationError::InvalidWire);
        }
        let claim = ComparisonClaim {
            protocol_id: cursor.digest()?,
            session_nonce: cursor.digest()?,
            roster_digest: cursor.digest()?,
            n_parties: cursor.u64()?,
            value_bits: cursor.u64()?,
            plaintext_modulus: cursor.u64()?,
            transcript_digest: cursor.digest()?,
            less_than: match cursor.u8()? {
                0 => false,
                1 => true,
                _ => return Err(DecisionAttestationError::InvalidWire),
            },
        };
        if claim.protocol_id != COMPARISON_ATTESTATION_PROTOCOL_ID {
            return Err(DecisionAttestationError::InvalidWire);
        }
        let computation_integrity = match cursor.u8()? {
            0 => ComputationIntegrityEvidence::BindingOnly(
                ComputationIntegrityResidual::OutputOnlySelfAssertion,
            ),
            1 => {
                let verifier_id = cursor.digest()?;
                let len = usize::try_from(cursor.u64()?)
                    .map_err(|_| DecisionAttestationError::InvalidWire)?;
                if len > MAX_EVIDENCE_BYTES {
                    return Err(DecisionAttestationError::EvidenceTooLarge);
                }
                ComputationIntegrityEvidence::External {
                    verifier_id,
                    evidence: cursor.take(len)?.to_vec(),
                }
            }
            _ => return Err(DecisionAttestationError::InvalidWire),
        };
        if cursor.offset != bytes.len() {
            return Err(DecisionAttestationError::InvalidWire);
        }
        Ok(Self {
            claim,
            computation_integrity,
        })
    }

    pub fn envelope_digest(&self) -> Result<Digest32> {
        Ok(domain_digest(
            COMPARISON_ENVELOPE_DOMAIN,
            &self.to_wire_bytes()?,
        ))
    }

    pub fn verify_binding(&self, expected: &ExpectedComparisonContext<'_>) -> Result<()> {
        if self.claim != comparison_claim_from_context(expected)? {
            return Err(DecisionAttestationError::BindingMismatch);
        }
        Ok(())
    }

    pub fn verify_full<V: ComputationIntegrityVerifier, R: ReplayGuard>(
        &self,
        expected: &ExpectedComparisonContext<'_>,
        verifier: &V,
        replay_guard: &mut R,
    ) -> Result<()> {
        self.verify_binding(expected)?;
        let (verifier_id, evidence) = match &self.computation_integrity {
            ComputationIntegrityEvidence::BindingOnly(residual) => {
                return Err(DecisionAttestationError::ComputationIntegrityResidual(
                    *residual,
                ));
            }
            ComputationIntegrityEvidence::External {
                verifier_id,
                evidence,
            } => (verifier_id, evidence),
        };
        if verifier_id != &verifier.verifier_id() {
            return Err(DecisionAttestationError::IntegrityVerifierMismatch);
        }
        if !verifier.verify(&self.claim.digest(), evidence) {
            return Err(DecisionAttestationError::InvalidComputationIntegrityEvidence);
        }
        if !replay_guard.check_and_record(self.replay_id()) {
            return Err(DecisionAttestationError::ReplayDetected);
        }
        Ok(())
    }

    fn replay_id(&self) -> Digest32 {
        let mut bytes = CanonicalBytes::default();
        bytes.digest(&self.claim.protocol_id);
        bytes.digest(&self.claim.session_nonce);
        bytes.digest(&self.claim.roster_digest);
        domain_digest(COMPARISON_REPLAY_DOMAIN, &bytes.finish())
    }
}

fn claim_from_context(context: &ExpectedDecisionContext<'_>) -> Result<DecisionClaim> {
    if !context.transcript.is_reveal_only(context.session) {
        return Err(DecisionAttestationError::TranscriptNotRevealOnly);
    }
    if context.transcript.revealed_equal != u8::from(context.equal) {
        return Err(DecisionAttestationError::TranscriptOutputMismatch);
    }
    Ok(DecisionClaim {
        protocol_id: DECISION_ATTESTATION_PROTOCOL_ID,
        session_nonce: context.session.nonce(),
        roster_digest: context.roster_digest,
        n_parties: context.session.n_parties() as u64,
        value_bits: context.session.value_bits() as u64,
        plaintext_modulus: context.session.plaintext_modulus(),
        transcript_digest: transcript_digest(context.transcript),
        equal: context.equal,
    })
}

fn comparison_claim_from_context(
    context: &ExpectedComparisonContext<'_>,
) -> Result<ComparisonClaim> {
    if !context.transcript.is_reveal_only(context.session) {
        return Err(DecisionAttestationError::TranscriptNotRevealOnly);
    }
    if context.transcript.revealed_less_than != u8::from(context.less_than) {
        return Err(DecisionAttestationError::TranscriptOutputMismatch);
    }
    Ok(ComparisonClaim {
        protocol_id: COMPARISON_ATTESTATION_PROTOCOL_ID,
        session_nonce: context.session.nonce(),
        roster_digest: context.roster_digest,
        n_parties: context.session.n_parties() as u64,
        value_bits: context.session.value_bits() as u64,
        plaintext_modulus: context.session.plaintext_modulus(),
        transcript_digest: comparison_transcript_digest(context.transcript),
        less_than: context.less_than,
    })
}

pub fn transcript_digest(transcript: &DecisionTranscript) -> Digest32 {
    let mut out = CanonicalBytes::default();
    out.u64(transcript.masked.len() as u64);
    for opening in &transcript.masked {
        out.u64(opening.gate as u64);
        out.u8(opening.d);
        out.u8(opening.e);
    }
    out.u8(transcript.revealed_equal);
    out.u64(transcript.and_gates as u64);
    out.u64(transcript.scalar_opening_rounds as u64);
    out.u64(transcript.modeled_batched_rounds as u64);
    out.u64(transcript.gate_share_messages as u64);
    out.u64(transcript.output_share_messages as u64);
    domain_digest(TRANSCRIPT_DOMAIN, &out.finish())
}

pub fn comparison_transcript_digest(transcript: &ComparisonTranscript) -> Digest32 {
    let mut out = CanonicalBytes::default();
    out.u64(transcript.masked.len() as u64);
    for opening in &transcript.masked {
        out.u64(opening.gate as u64);
        out.u8(opening.d);
        out.u8(opening.e);
    }
    out.u8(transcript.revealed_less_than);
    out.u64(transcript.and_gates as u64);
    out.u64(transcript.scalar_opening_rounds as u64);
    out.u64(transcript.modeled_batched_rounds as u64);
    out.u64(transcript.gate_share_messages as u64);
    out.u64(transcript.output_share_messages as u64);
    domain_digest(COMPARISON_TRANSCRIPT_DOMAIN, &out.finish())
}

struct WireCursor<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> WireCursor<'a> {
    fn take(&mut self, len: usize) -> Result<&'a [u8]> {
        let end = self
            .offset
            .checked_add(len)
            .ok_or(DecisionAttestationError::InvalidWire)?;
        let out = self
            .bytes
            .get(self.offset..end)
            .ok_or(DecisionAttestationError::InvalidWire)?;
        self.offset = end;
        Ok(out)
    }

    fn u8(&mut self) -> Result<u8> {
        Ok(self.take(1)?[0])
    }

    fn u64(&mut self) -> Result<u64> {
        Ok(u64::from_be_bytes(
            self.take(8)?
                .try_into()
                .map_err(|_| DecisionAttestationError::InvalidWire)?,
        ))
    }

    fn digest(&mut self) -> Result<Digest32> {
        self.take(32)?
            .try_into()
            .map_err(|_| DecisionAttestationError::InvalidWire)
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use ed25519_dalek::SigningKey;
    use rand::{rngs::StdRng, SeedableRng};

    use super::*;
    use crate::attestation::{AuthenticatedQuorumVerifier, InMemoryReplayGuard};
    use crate::mpc_party::simulate_decision_transcript;

    fn fixture(
        nonce: [u8; 32],
        equal: bool,
    ) -> (
        PartyMpcSession,
        DecisionTranscript,
        Vec<SigningKey>,
        AuthenticatedQuorumVerifier,
    ) {
        let session =
            PartyMpcSession::equality(nonce, 3, 17, 1_032_193, Duration::from_millis(250)).unwrap();
        let transcript =
            simulate_decision_transcript(equal, &session, &mut StdRng::seed_from_u64(17)).unwrap();
        let keys = vec![
            SigningKey::from_bytes(&[3; 32]),
            SigningKey::from_bytes(&[5; 32]),
            SigningKey::from_bytes(&[7; 32]),
        ];
        let verifier = AuthenticatedQuorumVerifier::new(
            keys.iter()
                .map(|key| key.verifying_key().to_bytes())
                .collect(),
            2,
        )
        .unwrap();
        (session, transcript, keys, verifier)
    }

    #[test]
    fn quorum_receipt_roundtrips_and_replays_fail_closed() {
        let (session, transcript, keys, verifier) = fixture([11; 32], true);
        let context = ExpectedDecisionContext {
            session: &session,
            roster_digest: verifier.roster_digest(),
            transcript: &transcript,
            equal: true,
        };
        let draft = AttestedDecisionReceipt::issue(
            &context,
            ComputationIntegrityEvidence::BindingOnly(
                ComputationIntegrityResidual::OutputOnlySelfAssertion,
            ),
        )
        .unwrap();
        let signatures = vec![
            verifier
                .sign_claim(&draft.claim_digest(), 0, &keys[0])
                .unwrap(),
            verifier
                .sign_claim(&draft.claim_digest(), 2, &keys[2])
                .unwrap(),
        ];
        let evidence = verifier
            .assemble_evidence(&draft.claim_digest(), &signatures)
            .unwrap();
        let receipt = AttestedDecisionReceipt::issue(&context, evidence).unwrap();
        let decoded =
            AttestedDecisionReceipt::from_wire_bytes(&receipt.to_wire_bytes().unwrap()).unwrap();
        assert_eq!(decoded, receipt);

        let mut replay = InMemoryReplayGuard::default();
        decoded
            .verify_full(&context, &verifier, &mut replay)
            .unwrap();
        assert_eq!(
            decoded.verify_full(&context, &verifier, &mut replay),
            Err(DecisionAttestationError::ReplayDetected)
        );
    }

    #[test]
    fn candidate_bit_transcript_and_evidence_substitution_are_refused() {
        let (session, transcript, keys, verifier) = fixture([13; 32], false);
        let context = ExpectedDecisionContext {
            session: &session,
            roster_digest: verifier.roster_digest(),
            transcript: &transcript,
            equal: false,
        };
        let draft = AttestedDecisionReceipt::issue(
            &context,
            ComputationIntegrityEvidence::BindingOnly(
                ComputationIntegrityResidual::OutputOnlySelfAssertion,
            ),
        )
        .unwrap();
        let signatures = vec![
            verifier
                .sign_claim(&draft.claim_digest(), 0, &keys[0])
                .unwrap(),
            verifier
                .sign_claim(&draft.claim_digest(), 1, &keys[1])
                .unwrap(),
        ];
        let evidence = verifier
            .assemble_evidence(&draft.claim_digest(), &signatures)
            .unwrap();
        let receipt = AttestedDecisionReceipt::issue(&context, evidence).unwrap();

        let (other_session, other_transcript, _, _) = fixture([14; 32], false);
        let other_context = ExpectedDecisionContext {
            session: &other_session,
            roster_digest: verifier.roster_digest(),
            transcript: &other_transcript,
            equal: false,
        };
        assert_eq!(
            receipt.verify_binding(&other_context),
            Err(DecisionAttestationError::BindingMismatch)
        );

        let wrong_bit_context = ExpectedDecisionContext {
            session: &session,
            roster_digest: verifier.roster_digest(),
            transcript: &transcript,
            equal: true,
        };
        assert_eq!(
            receipt.verify_binding(&wrong_bit_context),
            Err(DecisionAttestationError::TranscriptOutputMismatch)
        );

        let mut wire = receipt.to_wire_bytes().unwrap();
        *wire.last_mut().unwrap() ^= 1;
        let tampered = AttestedDecisionReceipt::from_wire_bytes(&wire).unwrap();
        assert_eq!(
            tampered.verify_full(&context, &verifier, &mut InMemoryReplayGuard::default()),
            Err(DecisionAttestationError::InvalidComputationIntegrityEvidence)
        );
    }

    #[test]
    fn decision_wire_is_canonical_bounded_and_exact_eof() {
        let (session, transcript, _, verifier) = fixture([19; 32], true);
        let context = ExpectedDecisionContext {
            session: &session,
            roster_digest: verifier.roster_digest(),
            transcript: &transcript,
            equal: true,
        };
        let binding_only = AttestedDecisionReceipt::issue(
            &context,
            ComputationIntegrityEvidence::BindingOnly(
                ComputationIntegrityResidual::OutputOnlySelfAssertion,
            ),
        )
        .unwrap();
        let wire = binding_only.to_wire_bytes().unwrap();
        assert_eq!(wire.len(), 162);

        // Every strict prefix is incomplete, and an otherwise valid envelope
        // with a suffix is non-canonical rather than prefix-accepted.
        for end in 0..wire.len() {
            assert_eq!(
                AttestedDecisionReceipt::from_wire_bytes(&wire[..end]),
                Err(DecisionAttestationError::InvalidWire),
                "prefix length {end}"
            );
        }
        let mut trailing = wire.clone();
        trailing.push(0);
        assert_eq!(
            AttestedDecisionReceipt::from_wire_bytes(&trailing),
            Err(DecisionAttestationError::InvalidWire)
        );

        let mut wrong_protocol = wire.clone();
        wrong_protocol[8] ^= 1;
        assert_eq!(
            AttestedDecisionReceipt::from_wire_bytes(&wrong_protocol),
            Err(DecisionAttestationError::InvalidWire)
        );
        let mut non_boolean = wire.clone();
        non_boolean[160] = 2;
        assert_eq!(
            AttestedDecisionReceipt::from_wire_bytes(&non_boolean),
            Err(DecisionAttestationError::InvalidWire)
        );
        let mut unknown_evidence = wire;
        unknown_evidence[161] = 2;
        assert_eq!(
            AttestedDecisionReceipt::from_wire_bytes(&unknown_evidence),
            Err(DecisionAttestationError::InvalidWire)
        );

        let external = AttestedDecisionReceipt::issue(
            &context,
            ComputationIntegrityEvidence::External {
                verifier_id: [23; 32],
                evidence: Vec::new(),
            },
        )
        .unwrap();
        let mut oversized_len = external.to_wire_bytes().unwrap();
        oversized_len[194..202].copy_from_slice(&((MAX_EVIDENCE_BYTES as u64) + 1).to_be_bytes());
        assert_eq!(
            AttestedDecisionReceipt::from_wire_bytes(&oversized_len),
            Err(DecisionAttestationError::EvidenceTooLarge)
        );
        let oversized = AttestedDecisionReceipt::issue(
            &context,
            ComputationIntegrityEvidence::External {
                verifier_id: [29; 32],
                evidence: vec![0; MAX_EVIDENCE_BYTES + 1],
            },
        )
        .unwrap();
        assert_eq!(
            oversized.to_wire_bytes(),
            Err(DecisionAttestationError::EvidenceTooLarge)
        );
    }
}
