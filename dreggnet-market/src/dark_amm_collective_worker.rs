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
use fhegg_fhe::amm_same_opening::canonical_bfv_parameters_digest;
use fhegg_fhe::attestation::{
    AuthenticatedQuorumVerifier, ComputationIntegrityEvidence, ComputationIntegrityResidual,
    PartyClaimSignature, QuorumVerifierError,
};
use fhegg_fhe::bfv_lean::LeanCiphertext;
use fhegg_fhe::bfv_mul::BoundedCiphertext;
use fhegg_fhe::boundary::{
    BoundaryError, EncryptedMaskContribution, MaskedBoundaryParty, MaskedDecryptCoordinator,
    MaskedDecryptSession, MaskedOpening,
};
use fhegg_fhe::dark_amm::{
    DarkPoolPublicHostMaterial, MAX_PRIVATE_DECISION_CARRIER_BYTES, PrivateAppliedSwap,
    PrivateAppliedSwapDecisionCarrier, PrivateDecisionCarrierError,
};
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

const COLLECTIVE_DECISION_TASK_MAGIC: &[u8; 8] = b"DBDTv001";
const COLLECTIVE_DECISION_TASK_CHECKSUM_DOMAIN: &str =
    "dregg-dark-amm-collective-decision-task-checksum-v1";
const COLLECTIVE_DECISION_TASK_DIGEST_DOMAIN: &str = "dregg-dark-amm-collective-decision-task-v1";
/// Complete public task size, dominated by its three BFV ciphertexts.
pub const MAX_COLLECTIVE_DECISION_TASK_BYTES: usize = MAX_PRIVATE_DECISION_CARRIER_BYTES + 1024;

/// Hosted state that must not be inferred from an untrusted worker task.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CollectiveDecisionTaskContext {
    pub hosted_session: [u8; 32],
    pub sequence: u64,
    pub committed_root: [u32; 8],
    pub same_opening_claim_digest: [u8; 32],
}

/// Strict task transport and independently pinned-identity failures.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CollectiveDecisionTaskError {
    TooLarge,
    InvalidWire(&'static str),
    InvalidContext(&'static str),
    ParameterMismatch,
    KeygenMismatch,
    CollectiveKeyMismatch,
    CommittedMaterialMismatch,
    DecisionShapeMismatch,
    Candidate(PrivateDecisionCarrierError),
}

impl fmt::Display for CollectiveDecisionTaskError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TooLarge => write!(f, "collective decision task exceeds its allocation limit"),
            Self::InvalidWire(reason) => write!(f, "invalid collective decision task: {reason}"),
            Self::InvalidContext(reason) => {
                write!(f, "invalid collective decision task context: {reason}")
            }
            Self::ParameterMismatch => write!(f, "decision task BFV parameters do not match"),
            Self::KeygenMismatch => write!(f, "decision task DKG identity does not match"),
            Self::CollectiveKeyMismatch => {
                write!(f, "decision task collective public key does not match")
            }
            Self::CommittedMaterialMismatch => {
                write!(f, "decision task committed material does not match")
            }
            Self::DecisionShapeMismatch => {
                write!(f, "decision task equality shape does not match")
            }
            Self::Candidate(error) => write!(f, "decision task candidate refused: {error}"),
        }
    }
}

impl std::error::Error for CollectiveDecisionTaskError {}

impl From<PrivateDecisionCarrierError> for CollectiveDecisionTaskError {
    fn from(error: PrivateDecisionCarrierError) -> Self {
        Self::Candidate(error)
    }
}

/// Canonical public work order for one independently hosted collective
/// decision. Its digest is the FHDAR/party-MPC session nonce.
///
/// The task carries a digest of committed material rather than duplicating its
/// potentially large public relinearization key. Parsing therefore requires
/// the worker's independently obtained canonical material and checks the exact
/// encrypted pre-state through the candidate carrier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CollectiveDecisionTask {
    context: CollectiveDecisionTaskContext,
    committed_material_digest: [u8; 32],
    parameter_digest: [u8; 32],
    keygen_parties: u64,
    keygen_crp_seed: [u8; 32],
    collective_public_key_digest: [u8; 32],
    value_bits: u64,
    candidate: PrivateAppliedSwapDecisionCarrier,
}

impl CollectiveDecisionTask {
    #[allow(clippy::too_many_arguments)]
    pub fn from_candidate(
        context: CollectiveDecisionTaskContext,
        committed_material: &DarkPoolPublicHostMaterial,
        params: &BfvParams,
        keygen: &KeygenSession,
        collective: &CollectivePublicKey,
        value_bits: usize,
        candidate: &PrivateAppliedSwap,
    ) -> std::result::Result<Self, CollectiveDecisionTaskError> {
        let task = Self {
            context,
            committed_material_digest: committed_material.material_digest(),
            parameter_digest: canonical_bfv_parameters_digest(params.arc()),
            keygen_parties: keygen.n_parties() as u64,
            keygen_crp_seed: keygen.crp_seed(),
            collective_public_key_digest: collective_public_key_digest(collective),
            value_bits: value_bits as u64,
            candidate: candidate.public_decision_carrier(params.arc(), committed_material)?,
        };
        task.validate(committed_material, params, keygen, collective, value_bits)?;
        if task.to_wire_bytes()?.len() > MAX_COLLECTIVE_DECISION_TASK_BYTES {
            return Err(CollectiveDecisionTaskError::TooLarge);
        }
        Ok(task)
    }

    pub const fn context(&self) -> CollectiveDecisionTaskContext {
        self.context
    }

    pub const fn candidate_nonce(&self) -> [u8; 32] {
        self.candidate.candidate_nonce()
    }

    pub const fn public_k(&self) -> u64 {
        self.candidate.public_k()
    }

    pub const fn value_bits(&self) -> u64 {
        self.value_bits
    }

    pub fn candidate_carrier(&self) -> &PrivateAppliedSwapDecisionCarrier {
        &self.candidate
    }

    /// Host-side equality check against a freshly reconstructed authoritative
    /// candidate. The task carrier itself has no conversion into host state.
    pub fn matches_candidate(&self, candidate: &PrivateAppliedSwap) -> bool {
        self.candidate.matches_candidate(candidate)
    }

    /// The exact contextual nonce signed by FHDAR authorities. Since it hashes
    /// the complete canonical wire, it covers table/round, committed material,
    /// public BFV/DKG/key identity, same-opening claim, and candidate carrier.
    pub fn attestation_nonce(&self) -> std::result::Result<[u8; 32], CollectiveDecisionTaskError> {
        let wire = self.to_wire_bytes()?;
        let mut hash = blake3::Hasher::new_derive_key(COLLECTIVE_DECISION_TASK_DIGEST_DOMAIN);
        hash.update(&(wire.len() as u64).to_le_bytes());
        hash.update(&wire);
        Ok(*hash.finalize().as_bytes())
    }

    pub fn validate_context(
        &self,
        expected: CollectiveDecisionTaskContext,
    ) -> std::result::Result<(), CollectiveDecisionTaskError> {
        if self.context != expected {
            return Err(CollectiveDecisionTaskError::InvalidContext(
                "hosted session, sequence, root, or same-opening claim differs",
            ));
        }
        Ok(())
    }

    pub fn invariant(
        &self,
        params: &BfvParams,
    ) -> std::result::Result<BoundedCiphertext, CollectiveDecisionTaskError> {
        Ok(self.candidate.invariant(params.arc())?)
    }

    pub fn to_wire_bytes(&self) -> std::result::Result<Vec<u8>, CollectiveDecisionTaskError> {
        let candidate = self.candidate.to_wire_bytes()?;
        let total = 8usize
            .checked_add(32 + 8 + 8 * 4 + 6 * 32 + 3 * 8 + candidate.len())
            .ok_or(CollectiveDecisionTaskError::TooLarge)?;
        if total > MAX_COLLECTIVE_DECISION_TASK_BYTES {
            return Err(CollectiveDecisionTaskError::TooLarge);
        }
        let mut out = Vec::with_capacity(total);
        out.extend_from_slice(COLLECTIVE_DECISION_TASK_MAGIC);
        out.extend_from_slice(&self.context.hosted_session);
        out.extend_from_slice(&self.context.sequence.to_le_bytes());
        for lane in self.context.committed_root {
            out.extend_from_slice(&lane.to_le_bytes());
        }
        out.extend_from_slice(&self.context.same_opening_claim_digest);
        out.extend_from_slice(&self.committed_material_digest);
        out.extend_from_slice(&self.parameter_digest);
        out.extend_from_slice(&self.keygen_parties.to_le_bytes());
        out.extend_from_slice(&self.keygen_crp_seed);
        out.extend_from_slice(&self.collective_public_key_digest);
        out.extend_from_slice(&self.value_bits.to_le_bytes());
        put_task_bytes(&mut out, &candidate);
        out.extend_from_slice(&collective_decision_task_checksum(&out));
        Ok(out)
    }

    pub fn from_wire_bytes(
        bytes: &[u8],
        committed_material: &DarkPoolPublicHostMaterial,
        params: &BfvParams,
        keygen: &KeygenSession,
        collective: &CollectivePublicKey,
        value_bits: usize,
    ) -> std::result::Result<Self, CollectiveDecisionTaskError> {
        if bytes.len() > MAX_COLLECTIVE_DECISION_TASK_BYTES {
            return Err(CollectiveDecisionTaskError::TooLarge);
        }
        const MIN_BYTES: usize = 8 + 32 + 8 + 8 * 4 + 5 * 32 + 3 * 8 + 32;
        if bytes.len() < MIN_BYTES {
            return Err(CollectiveDecisionTaskError::InvalidWire(
                "truncated fixed header",
            ));
        }
        let content_end = bytes.len() - 32;
        if bytes[content_end..] != collective_decision_task_checksum(&bytes[..content_end]) {
            return Err(CollectiveDecisionTaskError::InvalidWire(
                "checksum mismatch",
            ));
        }
        let mut input = TaskReader::new(&bytes[..content_end]);
        if input.array::<8>()? != *COLLECTIVE_DECISION_TASK_MAGIC {
            return Err(CollectiveDecisionTaskError::InvalidWire(
                "wrong version magic",
            ));
        }
        let hosted_session = input.array()?;
        let sequence = input.u64()?;
        let mut committed_root = [0u32; 8];
        for lane in &mut committed_root {
            *lane = input.u32()?;
        }
        let task = Self {
            context: CollectiveDecisionTaskContext {
                hosted_session,
                sequence,
                committed_root,
                same_opening_claim_digest: input.array()?,
            },
            committed_material_digest: input.array()?,
            parameter_digest: input.array()?,
            keygen_parties: input.u64()?,
            keygen_crp_seed: input.array()?,
            collective_public_key_digest: input.array()?,
            value_bits: input.u64()?,
            candidate: PrivateAppliedSwapDecisionCarrier::from_wire_bytes(
                input.bytes(MAX_PRIVATE_DECISION_CARRIER_BYTES)?,
                params.arc(),
            )?,
        };
        input.finish()?;
        task.validate(committed_material, params, keygen, collective, value_bits)?;
        if task.to_wire_bytes()? != bytes {
            return Err(CollectiveDecisionTaskError::InvalidWire(
                "wire is not canonical",
            ));
        }
        Ok(task)
    }

    fn validate(
        &self,
        committed_material: &DarkPoolPublicHostMaterial,
        params: &BfvParams,
        keygen: &KeygenSession,
        collective: &CollectivePublicKey,
        value_bits: usize,
    ) -> std::result::Result<(), CollectiveDecisionTaskError> {
        if self.context.hosted_session == [0; 32]
            || self.context.same_opening_claim_digest == [0; 32]
        {
            return Err(CollectiveDecisionTaskError::InvalidContext(
                "hosted session and same-opening claim must be nonzero",
            ));
        }
        if self.parameter_digest != canonical_bfv_parameters_digest(params.arc())
            || self.candidate.parameter_digest() != committed_material.parameter_digest()
        {
            return Err(CollectiveDecisionTaskError::ParameterMismatch);
        }
        if self.keygen_parties != keygen.n_parties() as u64
            || self.keygen_crp_seed != keygen.crp_seed()
        {
            return Err(CollectiveDecisionTaskError::KeygenMismatch);
        }
        if self.collective_public_key_digest != collective_public_key_digest(collective)
            || committed_material.public_key_bytes() != collective.pk.to_bytes()
        {
            return Err(CollectiveDecisionTaskError::CollectiveKeyMismatch);
        }
        if self.committed_material_digest != committed_material.material_digest() {
            return Err(CollectiveDecisionTaskError::CommittedMaterialMismatch);
        }
        self.candidate
            .validate_committed_pre_state(params.arc(), committed_material)?;
        if self.value_bits != value_bits as u64
            || self.keygen_parties < 2
            || !(1..=63).contains(&value_bits)
            || params.plaintext_modulus() < (1u64 << value_bits)
            || self.candidate.invariant_bound() >= (1u64 << value_bits)
        {
            return Err(CollectiveDecisionTaskError::DecisionShapeMismatch);
        }
        Ok(())
    }
}

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
    Task(CollectiveDecisionTaskError),
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
            Self::Task(error) => write!(f, "collective decision task refused: {error}"),
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

impl From<CollectiveDecisionTaskError> for CollectiveDecisionWorkerError {
    fn from(error: CollectiveDecisionTaskError) -> Self {
        Self::Task(error)
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
    keygen: &'a KeygenSession,
    collective: &'a CollectivePublicKey,
    parties: &'a [ThresholdParty],
    value_bits: usize,
    timeout: Duration,
}

impl<'a> MaskedCollectiveDecisionWorker<'a> {
    pub fn new(
        params: &'a BfvParams,
        keygen: &'a KeygenSession,
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
            keygen,
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

    /// Reconstruct the task-digest session after checking every independently
    /// configured BFV/DKG/collective identity field.
    pub fn decision_session_for_task(
        &self,
        task: &CollectiveDecisionTask,
        committed_material: &DarkPoolPublicHostMaterial,
        expected_context: CollectiveDecisionTaskContext,
    ) -> Result<PartyMpcSession> {
        task.validate_context(expected_context)?;
        task.validate(
            committed_material,
            self.params,
            self.keygen,
            self.collective,
            self.value_bits,
        )?;
        Ok(PartyMpcSession::equality(
            task.attestation_nonce()?,
            self.parties.len(),
            self.value_bits,
            self.params.plaintext_modulus(),
            self.timeout,
        )?)
    }

    /// Decide a strict cross-process task. The resulting transcript and FHDAR
    /// claim use the task digest—not the context-free candidate nonce—as their
    /// session nonce.
    pub fn decide_task_with_triples(
        &self,
        task: &CollectiveDecisionTask,
        committed_material: &DarkPoolPublicHostMaterial,
        expected_context: CollectiveDecisionTaskContext,
        triples: Vec<TripleMaterial>,
    ) -> Result<MaskedCollectiveDecision> {
        let session = self.decision_session_for_task(task, committed_material, expected_context)?;
        let invariant = task.invariant(self.params)?;
        self.decide_target_with_triples(session, &invariant, task.public_k(), triples)
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
        let session = self.decision_session(candidate)?;
        self.decide_target_with_triples(session, &candidate.invariant, public_k, triples)
    }

    fn decide_target_with_triples(
        &self,
        equality_session: PartyMpcSession,
        invariant: &BoundedCiphertext,
        public_k: u64,
        triples: Vec<TripleMaterial>,
    ) -> Result<MaskedCollectiveDecision> {
        let range_end = 1u64
            .checked_shl(self.value_bits as u32)
            .ok_or(CollectiveDecisionWorkerError::PublicTargetOutOfRange)?;
        if public_k >= range_end
            || public_k >= self.params.plaintext_modulus()
            || invariant.plain_bound >= range_end
        {
            return Err(CollectiveDecisionWorkerError::PublicTargetOutOfRange);
        }
        if triples.len() != self.parties.len() {
            return Err(CollectiveDecisionWorkerError::PreprocessingShape {
                have: triples.len(),
                need: self.parties.len(),
            });
        }
        let target = LeanCiphertext::from_fhe_bytes(
            &invariant.ct.to_bytes(),
            self.params.moduli(),
            self.params.degree(),
            invariant.plain_bound,
        )
        .map_err(|_| CollectiveDecisionWorkerError::CandidateCiphertextMalformed)?;
        let mask_session = MaskedDecryptSession::from_public(
            equality_session.nonce(),
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

fn collective_public_key_digest(collective: &CollectivePublicKey) -> [u8; 32] {
    let bytes = collective.pk.to_bytes();
    let mut hash =
        blake3::Hasher::new_derive_key("dregg-dark-amm-collective-decision-task-public-key-v1");
    hash.update(&(bytes.len() as u64).to_le_bytes());
    hash.update(&bytes);
    *hash.finalize().as_bytes()
}

fn collective_decision_task_checksum(content: &[u8]) -> [u8; 32] {
    let mut hash = blake3::Hasher::new_derive_key(COLLECTIVE_DECISION_TASK_CHECKSUM_DOMAIN);
    hash.update(&(content.len() as u64).to_le_bytes());
    hash.update(content);
    *hash.finalize().as_bytes()
}

fn put_task_bytes(out: &mut Vec<u8>, bytes: &[u8]) {
    out.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
    out.extend_from_slice(bytes);
}

struct TaskReader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> TaskReader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn array<const N: usize>(
        &mut self,
    ) -> std::result::Result<[u8; N], CollectiveDecisionTaskError> {
        let end = self
            .offset
            .checked_add(N)
            .filter(|end| *end <= self.bytes.len())
            .ok_or(CollectiveDecisionTaskError::InvalidWire(
                "truncated fixed-width field",
            ))?;
        let value = self.bytes[self.offset..end]
            .try_into()
            .map_err(|_| CollectiveDecisionTaskError::InvalidWire("invalid fixed-width field"))?;
        self.offset = end;
        Ok(value)
    }

    fn u32(&mut self) -> std::result::Result<u32, CollectiveDecisionTaskError> {
        Ok(u32::from_le_bytes(self.array()?))
    }

    fn u64(&mut self) -> std::result::Result<u64, CollectiveDecisionTaskError> {
        Ok(u64::from_le_bytes(self.array()?))
    }

    fn bytes(&mut self, max: usize) -> std::result::Result<&'a [u8], CollectiveDecisionTaskError> {
        let len = usize::try_from(self.u64()?)
            .map_err(|_| CollectiveDecisionTaskError::InvalidWire("length does not fit usize"))?;
        if len > max {
            return Err(CollectiveDecisionTaskError::InvalidWire(
                "length-delimited field exceeds its limit",
            ));
        }
        let end = self
            .offset
            .checked_add(len)
            .filter(|end| *end <= self.bytes.len())
            .ok_or(CollectiveDecisionTaskError::InvalidWire(
                "truncated length-delimited field",
            ))?;
        let value = &self.bytes[self.offset..end];
        self.offset = end;
        Ok(value)
    }

    fn finish(self) -> std::result::Result<(), CollectiveDecisionTaskError> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err(CollectiveDecisionTaskError::InvalidWire("trailing bytes"))
        }
    }
}
