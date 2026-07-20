//! Cross-process authorization for an encrypted Dark AMM candidate.
//!
//! Candidate evaluation and the collective decision need not live in one
//! process. A secretless host retains a [`PrivateAppliedSwap`]; custodians run
//! the masked-decrypt/equality protocol elsewhere and return its public
//! reveal-only transcript plus an [`AttestedDecisionReceipt`]. This module
//! reconstructs the equality session only from host policy and an independently
//! expected candidate/task nonce, verifies configured quorum evidence and
//! replay, then installs the already-encrypted state. Hosted collective tables
//! use the digest of their complete canonical worker task so a receipt cannot
//! migrate across table sessions or sequences.
//!
//! This is not threshold decryption and never accepts a BFV secret key or
//! decryption share. Quorum signatures authenticate agreement on the bit; they
//! do not prove malicious-secure share formation or the initial pool opening.
//! A deployment must bind the initial [`crate::dark_amm::DarkPoolPublicHostMaterial`]
//! to trusted creation evidence and persist the advanced pool state together
//! with durable replay state in one transaction.

use std::fmt;
use std::time::Duration;

use crate::attestation::{AuthenticatedQuorumVerifier, ReplayGuard};
use crate::dark_amm::{DarkAmmError, DarkPool, PrivateAppliedSwap};
use crate::decision_attestation::{
    AttestedDecisionReceipt, DecisionAttestationError, ExpectedDecisionContext,
};
use crate::mpc_party::{DecisionTranscript, PartyMpcError, PartyMpcSession};

/// Independently configured relying-party policy for Dark AMM decisions.
///
/// The party count is derived from the exact ordered quorum roster rather than
/// copied from an untrusted receipt. The value width and plaintext modulus are
/// likewise host configuration; receipt fields must match them exactly.
#[derive(Clone, Debug)]
pub struct AttestedPrivateDecisionPolicy {
    value_bits: usize,
    plaintext_modulus: u64,
    quorum_timeout: Duration,
    verifier: AuthenticatedQuorumVerifier,
}

impl AttestedPrivateDecisionPolicy {
    pub fn new(
        value_bits: usize,
        plaintext_modulus: u64,
        quorum_timeout: Duration,
        verifier: AuthenticatedQuorumVerifier,
    ) -> Result<Self, AttestedPrivateCommitError> {
        // Validate the complete public circuit shape at configuration time.
        PartyMpcSession::equality(
            [0; 32],
            verifier.ordered_public_keys().len(),
            value_bits,
            plaintext_modulus,
            quorum_timeout,
        )?;
        Ok(Self {
            value_bits,
            plaintext_modulus,
            quorum_timeout,
            verifier,
        })
    }

    pub fn n_parties(&self) -> usize {
        self.verifier.ordered_public_keys().len()
    }

    pub fn value_bits(&self) -> usize {
        self.value_bits
    }

    pub fn plaintext_modulus(&self) -> u64 {
        self.plaintext_modulus
    }

    pub fn verifier(&self) -> &AuthenticatedQuorumVerifier {
        &self.verifier
    }

    fn session(&self, candidate_nonce: [u8; 32]) -> Result<PartyMpcSession, PartyMpcError> {
        PartyMpcSession::equality(
            candidate_nonce,
            self.n_parties(),
            self.value_bits,
            self.plaintext_modulus,
            self.quorum_timeout,
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AttestedPrivateCommitError {
    /// The collective explicitly refused the invariant.
    DecisionRefused,
    /// The relying-party policy names a BFV scalar domain different from the
    /// pool being mutated.
    PoolPlaintextModulusMismatch {
        pool: u64,
        policy: u64,
    },
    /// The encrypted candidate's public worst-case bound does not fit the
    /// equality circuit's declared bit width. Accepting it would let the
    /// authorities attest equality only after truncation.
    CandidateRangeExceedsDecisionWidth {
        candidate_bound: u64,
        range_end: u64,
    },
    Candidate(DarkAmmCommitPreflightError),
    Session(PartyMpcError),
    Attestation(DecisionAttestationError),
}

/// Stable public classification of candidate/pool preflight refusals. This
/// avoids exposing internal FHE errors while preserving the refusal reason.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DarkAmmCommitPreflightError {
    HouseViewRequired,
    CandidateContextMismatch,
    Other,
}

impl fmt::Display for AttestedPrivateCommitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DecisionRefused => write!(f, "attested Dark AMM decision refused the candidate"),
            Self::PoolPlaintextModulusMismatch { pool, policy } => write!(
                f,
                "attested Dark AMM policy plaintext modulus {policy} does not match pool {pool}"
            ),
            Self::CandidateRangeExceedsDecisionWidth {
                candidate_bound,
                range_end,
            } => write!(
                f,
                "Dark AMM candidate bound {candidate_bound} is outside the decision circuit range 0..{range_end}"
            ),
            Self::Candidate(reason) => {
                write!(f, "Dark AMM candidate preflight refused: {reason:?}")
            }
            Self::Session(error) => write!(f, "Dark AMM equality session refused: {error}"),
            Self::Attestation(error) => write!(f, "Dark AMM attestation refused: {error}"),
        }
    }
}

impl std::error::Error for AttestedPrivateCommitError {}

impl From<PartyMpcError> for AttestedPrivateCommitError {
    fn from(error: PartyMpcError) -> Self {
        Self::Session(error)
    }
}

impl From<DecisionAttestationError> for AttestedPrivateCommitError {
    fn from(error: DecisionAttestationError) -> Self {
        Self::Attestation(error)
    }
}

fn candidate_preflight_error(error: DarkAmmError) -> AttestedPrivateCommitError {
    let reason = match error {
        DarkAmmError::PrivateSwapRequiresHouseView => {
            DarkAmmCommitPreflightError::HouseViewRequired
        }
        DarkAmmError::InvariantDecisionContextMismatch => {
            DarkAmmCommitPreflightError::CandidateContextMismatch
        }
        _ => DarkAmmCommitPreflightError::Other,
    };
    AttestedPrivateCommitError::Candidate(reason)
}

/// Verify a durable independently produced equality decision and install its
/// encrypted candidate without a [`crate::mpc_party::DistributedDecisionRun`].
///
/// All pool, policy, transcript, output-bit, and evidence checks occur before
/// [`ReplayGuard::check_and_record`]. The receipt verifier itself consumes the
/// replay id last; encrypted-state installation after it is infallible.
pub fn commit_attested_private_decision<R: ReplayGuard>(
    pool: &mut DarkPool,
    candidate: &PrivateAppliedSwap,
    policy: &AttestedPrivateDecisionPolicy,
    transcript: &DecisionTranscript,
    receipt: &AttestedDecisionReceipt,
    replay_guard: &mut R,
) -> Result<(), AttestedPrivateCommitError> {
    commit_attested_private_decision_in_context(
        pool,
        candidate,
        candidate.decision_session_nonce(),
        policy,
        transcript,
        receipt,
        replay_guard,
    )
}

/// Verify and install a candidate whose FHDAR session nonce is an independently
/// reconstructed contextual task digest.
///
/// The ordinary helper above uses the candidate nonce directly. Collective
/// hosted services should instead hash the complete canonical worker task—
/// including hosted session, sequence, committed material, public collective
/// identity, and exact candidate carrier—and supply that digest here. This
/// makes the existing FHDAR `session_nonce` field bind the larger context
/// without adding a second optional claim field or accepting legacy ambiguity.
#[allow(clippy::too_many_arguments)]
pub fn commit_attested_private_decision_in_context<R: ReplayGuard>(
    pool: &mut DarkPool,
    candidate: &PrivateAppliedSwap,
    decision_session_nonce: [u8; 32],
    policy: &AttestedPrivateDecisionPolicy,
    transcript: &DecisionTranscript,
    receipt: &AttestedDecisionReceipt,
    replay_guard: &mut R,
) -> Result<(), AttestedPrivateCommitError> {
    pool.preflight_private_candidate(candidate)
        .map_err(candidate_preflight_error)?;
    let pool_t = pool.plaintext_modulus();
    if policy.plaintext_modulus != pool_t {
        return Err(AttestedPrivateCommitError::PoolPlaintextModulusMismatch {
            pool: pool_t,
            policy: policy.plaintext_modulus,
        });
    }
    let range_end = 1u64 << policy.value_bits;
    if candidate.invariant.plain_bound >= range_end {
        return Err(
            AttestedPrivateCommitError::CandidateRangeExceedsDecisionWidth {
                candidate_bound: candidate.invariant.plain_bound,
                range_end,
            },
        );
    }
    if !receipt.claim.equal || transcript.revealed_equal != 1 {
        return Err(AttestedPrivateCommitError::DecisionRefused);
    }

    let session = policy.session(decision_session_nonce)?;
    let expected = ExpectedDecisionContext {
        session: &session,
        roster_digest: policy.verifier.roster_digest(),
        transcript,
        equal: true,
    };
    receipt.verify_full(&expected, &policy.verifier, replay_guard)?;

    // Every fallible check, including replay acceptance, is complete.
    pool.install_preflighted_private_candidate(candidate);
    Ok(())
}
