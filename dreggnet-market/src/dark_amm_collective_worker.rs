//! Custodian-side, no-assembled-secret Dark AMM decision worker.
//!
//! A public-only table can produce a [`PrivateAppliedSwap`] but cannot decide
//! whether its encrypted invariant equals the public pool invariant. This
//! worker supplies that missing phase without ever constructing a BFV secret
//! key or opening the invariant itself:
//!
//! 1. every custodian encrypts and retains a fresh one-time pad;
//! 2. the coordinator threshold-opens only `invariant + sum(pads)`;
//! 3. every custodian locally removes only its own pad into a mod-`t` share;
//! 4. the peer-distributed equality circuit releases one bit; and
//! 5. independently held Ed25519 authorities can endorse the exact public
//!    reveal-only transcript for transport back to the table.
//!
//! The worker is n-of-n and semi-honest. [`TripleMaterial`] remains an explicit
//! input because production preprocessing is a deployment choice: callers must
//! supply private, correctly correlated Beaver material. The shape-only trusted
//! dealer helper is suitable for integration tests, not a production dealer.
//! Quorum signatures authenticate roster agreement on the released bit; they
//! do not prove maliciously correct mask/share formation.

use std::fmt;
use std::sync::mpsc::{self, Receiver, RecvTimeoutError, Sender};
use std::thread;
use std::time::Duration;

use fhe_traits::Serialize as FheSerialize;
use fhegg_fhe::attestation::{
    AuthenticatedQuorumVerifier, ComputationIntegrityEvidence, ComputationIntegrityResidual,
    PartyClaimSignature, QuorumVerifierError,
};
use fhegg_fhe::bfv_lean::LeanCiphertext;
use fhegg_fhe::boundary::{
    BoundaryError, EncryptedMaskContribution, MaskedBoundaryParty, MaskedDecryptCoordinator,
    MaskedDecryptSession, MaskedOpening,
};
use fhegg_fhe::dark_amm::PrivateAppliedSwap;
use fhegg_fhe::decision_attestation::{
    AttestedDecisionReceipt, DecisionAttestationError, ExpectedDecisionContext,
};
use fhegg_fhe::mpc_party::{
    DecisionTranscript, PartyChannels, PartyEqualityInput, PartyMpcError, PartyMpcSession,
    TripleMaterial, local_channels, run_party_equality,
};
use fhegg_fhe::threshold::{
    BfvParams, CollectivePublicKey, KeygenSession, MIN_SMUDGE_BITS, ThresholdError, ThresholdParty,
};
use rand::rngs::OsRng;

/// A production worker should not permit unbounded waits on a failed custodian.
pub const MAX_COLLECTIVE_DECISION_TIMEOUT: Duration = Duration::from_secs(5 * 60);

/// Fail-closed worker and attestation errors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CollectiveDecisionWorkerError {
    InvalidConfiguration(&'static str),
    PublicTargetOutOfRange,
    CandidateCiphertextMalformed,
    PreprocessingShape { have: usize, need: usize },
    ChannelTimeout(&'static str),
    ChannelClosed(&'static str),
    Boundary(BoundaryError),
    Threshold(ThresholdError),
    Mpc(PartyMpcError),
    RosterMismatch { have: usize, need: usize },
    Quorum(QuorumVerifierError),
    Attestation(DecisionAttestationError),
    WorkerPanicked,
}

impl fmt::Display for CollectiveDecisionWorkerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidConfiguration(reason) => {
                write!(
                    f,
                    "invalid collective decision worker configuration: {reason}"
                )
            }
            Self::PublicTargetOutOfRange => {
                write!(
                    f,
                    "public invariant target is outside the declared equality range"
                )
            }
            Self::CandidateCiphertextMalformed => {
                write!(
                    f,
                    "candidate invariant ciphertext failed the strict BFV boundary"
                )
            }
            Self::PreprocessingShape { have, need } => write!(
                f,
                "collective decision preprocessing has {have} party rows, expected {need}"
            ),
            Self::ChannelTimeout(phase) => {
                write!(f, "collective decision timed out during {phase}")
            }
            Self::ChannelClosed(phase) => {
                write!(f, "collective decision channel closed during {phase}")
            }
            Self::Boundary(error) => write!(f, "masked-decrypt boundary refused: {error:?}"),
            Self::Threshold(error) => write!(f, "threshold custodian refused: {error:?}"),
            Self::Mpc(error) => write!(f, "party equality refused: {error}"),
            Self::RosterMismatch { have, need } => write!(
                f,
                "decision authority roster has {have} keys, expected {need}"
            ),
            Self::Quorum(error) => write!(f, "decision authority quorum refused: {error}"),
            Self::Attestation(error) => write!(f, "decision receipt refused: {error}"),
            Self::WorkerPanicked => write!(f, "a collective decision custodian panicked"),
        }
    }
}

impl std::error::Error for CollectiveDecisionWorkerError {}

impl From<BoundaryError> for CollectiveDecisionWorkerError {
    fn from(error: BoundaryError) -> Self {
        Self::Boundary(error)
    }
}

impl From<ThresholdError> for CollectiveDecisionWorkerError {
    fn from(error: ThresholdError) -> Self {
        Self::Threshold(error)
    }
}

impl From<PartyMpcError> for CollectiveDecisionWorkerError {
    fn from(error: PartyMpcError) -> Self {
        Self::Mpc(error)
    }
}

impl From<QuorumVerifierError> for CollectiveDecisionWorkerError {
    fn from(error: QuorumVerifierError) -> Self {
        Self::Quorum(error)
    }
}

impl From<DecisionAttestationError> for CollectiveDecisionWorkerError {
    fn from(error: DecisionAttestationError) -> Self {
        Self::Attestation(error)
    }
}

type Result<T> = std::result::Result<T, CollectiveDecisionWorkerError>;

struct EqualityCommand {
    opening: MaskedOpening,
    session: PartyMpcSession,
    public_target_share: u64,
    triples: TripleMaterial,
    channels: PartyChannels,
}

/// Exact custodian roster and equality shape for one collective table.
///
/// `ThresholdParty` has no clone, serialization, debug, or secret accessor.
/// Keeping the roster borrowed prevents this coordinator from accidentally
/// becoming a key-custody snapshot.
pub struct MaskedCollectiveDecisionWorker<'a> {
    params: &'a BfvParams,
    collective: &'a CollectivePublicKey,
    parties: &'a [ThresholdParty],
    value_bits: usize,
    timeout: Duration,
}

impl<'a> MaskedCollectiveDecisionWorker<'a> {
    pub fn new(
        params: &'a BfvParams,
        keygen: &KeygenSession,
        collective: &'a CollectivePublicKey,
        parties: &'a [ThresholdParty],
        value_bits: usize,
        timeout: Duration,
    ) -> Result<Self> {
        if parties.len() < 2 {
            return Err(CollectiveDecisionWorkerError::InvalidConfiguration(
                "party MPC requires at least two custodians",
            ));
        }
        if keygen.n_parties() != parties.len() {
            return Err(CollectiveDecisionWorkerError::InvalidConfiguration(
                "key-generation party count differs from the custodian roster",
            ));
        }
        if parties
            .iter()
            .enumerate()
            .any(|(expected, party)| party.party() != expected)
        {
            return Err(CollectiveDecisionWorkerError::InvalidConfiguration(
                "custodians must be in exact key-generation party order",
            ));
        }
        if timeout.is_zero() || timeout > MAX_COLLECTIVE_DECISION_TIMEOUT {
            return Err(CollectiveDecisionWorkerError::InvalidConfiguration(
                "timeout must be nonzero and at most five minutes",
            ));
        }
        // This validates the complete equality shape, including value width,
        // modulus capacity, party count, and gate-count overflow.
        PartyMpcSession::equality(
            [0; 32],
            parties.len(),
            value_bits,
            params.plaintext_modulus(),
            timeout,
        )?;

        Ok(Self {
            params,
            collective,
            parties,
            value_bits,
            timeout,
        })
    }

    pub fn n_parties(&self) -> usize {
        self.parties.len()
    }

    /// Independently reconstruct the exact candidate-bound public MPC session.
    /// A preprocessing service can use this value to mint session-specific
    /// private Beaver rows before calling [`Self::decide_with_triples`].
    pub fn decision_session(&self, candidate: &PrivateAppliedSwap) -> Result<PartyMpcSession> {
        Ok(PartyMpcSession::equality(
            candidate.decision_session_nonce(),
            self.parties.len(),
            self.value_bits,
            self.params.plaintext_modulus(),
            self.timeout,
        )?)
    }

    /// Decide one candidate using externally supplied, correctly correlated
    /// Beaver material. Only the one-time-padded opening reaches the
    /// coordinator; every unpadded operand remains distributed.
    pub fn decide_with_triples(
        &self,
        candidate: &PrivateAppliedSwap,
        public_k: u64,
        triples: Vec<TripleMaterial>,
    ) -> Result<MaskedCollectiveDecision> {
        let range_end = 1u64
            .checked_shl(self.value_bits as u32)
            .ok_or(CollectiveDecisionWorkerError::PublicTargetOutOfRange)?;
        if public_k >= range_end
            || public_k >= self.params.plaintext_modulus()
            || candidate.invariant.plain_bound >= range_end
        {
            return Err(CollectiveDecisionWorkerError::PublicTargetOutOfRange);
        }
        if triples.len() != self.parties.len() {
            return Err(CollectiveDecisionWorkerError::PreprocessingShape {
                have: triples.len(),
                need: self.parties.len(),
            });
        }

        let equality_session = self.decision_session(candidate)?;
        let target = LeanCiphertext::from_fhe_bytes(
            &candidate.invariant.ct.to_bytes(),
            self.params.moduli(),
            self.params.degree(),
            candidate.invariant.plain_bound,
        )
        .map_err(|_| CollectiveDecisionWorkerError::CandidateCiphertextMalformed)?;
        let mask_session = MaskedDecryptSession::from_public(
            candidate.decision_session_nonce(),
            self.parties.len(),
            1,
            target,
            self.params,
        )?;

        thread::scope(|scope| {
            let (mask_tx, mask_rx) = mpsc::channel::<EncryptedMaskContribution>();
            let (decrypt_tx, decrypt_rx) = mpsc::channel::<(usize, Vec<u8>)>();
            let mut decrypt_commands = Vec::with_capacity(self.parties.len());
            let mut equality_commands = Vec::with_capacity(self.parties.len());
            let mut workers = Vec::with_capacity(self.parties.len());

            for threshold_party in self.parties {
                let party_index = threshold_party.party();
                let (decrypt_command_tx, decrypt_command_rx) = mpsc::channel::<LeanCiphertext>();
                let (equality_command_tx, equality_command_rx) = mpsc::channel::<EqualityCommand>();
                decrypt_commands.push(decrypt_command_tx);
                equality_commands.push(equality_command_tx);
                let mask_tx = mask_tx.clone();
                let decrypt_tx = decrypt_tx.clone();
                let mask_session = mask_session.clone();
                let params = self.params;
                let collective = self.collective;
                let timeout = self.timeout;
                workers.push(scope.spawn(move || -> Result<()> {
                    let (mask_state, contribution) = MaskedBoundaryParty::prepare(
                        &mask_session,
                        party_index,
                        params,
                        collective,
                    )?;
                    send(&mask_tx, contribution, "mask contribution")?;

                    let masked_ciphertext =
                        receive(&decrypt_command_rx, timeout, "masked decrypt command")?;
                    let decrypt_share =
                        threshold_party.partial_decrypt(&masked_ciphertext, MIN_SMUDGE_BITS)?;
                    send(
                        &decrypt_tx,
                        (party_index, decrypt_share.to_wire_bytes()),
                        "threshold decrypt share",
                    )?;

                    let command = receive(&equality_command_rx, timeout, "equality command")?;
                    let left_share = mask_state.derive_mod_t_share(&command.opening)?[0];
                    let mut private_rng = OsRng;
                    let input = PartyEqualityInput::new(
                        &command.session,
                        party_index,
                        left_share,
                        command.public_target_share,
                        &mut private_rng,
                    )?;
                    run_party_equality(input, command.triples, command.channels)?;
                    Ok(())
                }));
            }
            drop(mask_tx);
            drop(decrypt_tx);

            let mut contributions = (0..self.parties.len())
                .map(|_| receive(&mask_rx, self.timeout, "mask contribution quorum"))
                .collect::<Result<Vec<_>>>()?;
            contributions.sort_by_key(EncryptedMaskContribution::party);
            let mut mask_coordinator =
                MaskedDecryptCoordinator::new(mask_session, self.params.clone());
            for contribution in contributions {
                mask_coordinator.accept(contribution)?;
            }
            let masked = mask_coordinator.finish()?;
            for command in &decrypt_commands {
                send(
                    command,
                    masked.ciphertext().clone(),
                    "masked decrypt command",
                )?;
            }

            let mut decrypt_shares = (0..self.parties.len())
                .map(|_| receive(&decrypt_rx, self.timeout, "threshold decrypt quorum"))
                .collect::<Result<Vec<_>>>()?;
            decrypt_shares.sort_by_key(|(party, _)| *party);
            let framed = decrypt_shares
                .into_iter()
                .map(|(_, share)| share)
                .collect::<Vec<_>>();
            let opening = masked.open_framed(&framed, self.params)?;

            let (coordinator, endpoints) = local_channels(&equality_session);
            for (party, ((command, triples), channels)) in equality_commands
                .into_iter()
                .zip(triples)
                .zip(endpoints)
                .enumerate()
            {
                send(
                    &command,
                    EqualityCommand {
                        opening: opening.clone(),
                        session: equality_session.clone(),
                        public_target_share: if party == 0 { public_k } else { 0 },
                        triples,
                        channels,
                    },
                    "equality command",
                )?;
            }

            let distributed = coordinator.coordinate_equality(&equality_session)?;
            for worker in workers {
                worker
                    .join()
                    .map_err(|_| CollectiveDecisionWorkerError::WorkerPanicked)??;
            }
            let equal = distributed.is_equal();
            Ok(MaskedCollectiveDecision {
                session: equality_session,
                transcript: distributed.transcript,
                equal,
            })
        })
    }
}

/// Public output of the private collective decision. It retains no ciphertext,
/// masked opening, mask, decryption share, operand share, or Beaver material.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MaskedCollectiveDecision {
    session: PartyMpcSession,
    transcript: DecisionTranscript,
    equal: bool,
}

impl MaskedCollectiveDecision {
    pub fn session(&self) -> &PartyMpcSession {
        &self.session
    }

    pub fn transcript(&self) -> &DecisionTranscript {
        &self.transcript
    }

    pub fn is_equal(&self) -> bool {
        self.equal
    }

    /// Issue the canonical binding-only draft whose digest authorities sign.
    /// The draft is intentionally not sufficient for relying-party acceptance.
    pub fn draft_receipt(
        &self,
        verifier: &AuthenticatedQuorumVerifier,
    ) -> Result<AttestedDecisionReceipt> {
        self.validate_roster(verifier)?;
        Ok(AttestedDecisionReceipt::issue(
            &self.expected_context(verifier),
            ComputationIntegrityEvidence::BindingOnly(
                ComputationIntegrityResidual::OutputOnlySelfAssertion,
            ),
        )?)
    }

    /// Assemble already-independent party signatures into the strict FHDAR
    /// receipt consumed by the public-only Dark AMM table.
    pub fn assemble_attested_receipt(
        &self,
        verifier: &AuthenticatedQuorumVerifier,
        signatures: &[PartyClaimSignature],
    ) -> Result<AttestedDecisionReceipt> {
        self.validate_roster(verifier)?;
        let draft = self.draft_receipt(verifier)?;
        let evidence = verifier.assemble_evidence(&draft.claim_digest(), signatures)?;
        let receipt = AttestedDecisionReceipt::issue(&self.expected_context(verifier), evidence)?;
        // Exercise the strict transport parser at the producer boundary so an
        // encoder/parser drift cannot first appear at the table.
        Ok(AttestedDecisionReceipt::from_wire_bytes(
            &receipt.to_wire_bytes()?,
        )?)
    }

    fn validate_roster(&self, verifier: &AuthenticatedQuorumVerifier) -> Result<()> {
        let have = verifier.ordered_public_keys().len();
        let need = self.session.n_parties();
        if have != need {
            return Err(CollectiveDecisionWorkerError::RosterMismatch { have, need });
        }
        Ok(())
    }

    fn expected_context<'a>(
        &'a self,
        verifier: &AuthenticatedQuorumVerifier,
    ) -> ExpectedDecisionContext<'a> {
        ExpectedDecisionContext {
            session: &self.session,
            roster_digest: verifier.roster_digest(),
            transcript: &self.transcript,
            equal: self.equal,
        }
    }
}

fn send<T>(sender: &Sender<T>, message: T, phase: &'static str) -> Result<()> {
    sender
        .send(message)
        .map_err(|_| CollectiveDecisionWorkerError::ChannelClosed(phase))
}

fn receive<T>(receiver: &Receiver<T>, timeout: Duration, phase: &'static str) -> Result<T> {
    receiver.recv_timeout(timeout).map_err(|error| match error {
        RecvTimeoutError::Timeout => CollectiveDecisionWorkerError::ChannelTimeout(phase),
        RecvTimeoutError::Disconnected => CollectiveDecisionWorkerError::ChannelClosed(phase),
    })
}
