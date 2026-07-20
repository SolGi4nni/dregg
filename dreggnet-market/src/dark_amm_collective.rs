//! Public-only, two-phase collective Dark AMM session.
//!
//! Phase one accepts the existing strict-v3 request, but reconstructs its
//! Tier-1 same-opening claim under the configured *collective* DKG identity
//! instead of the single-host `n=1` identity used by `dark_amm_game`. It checks
//! the same-opening replay slot without consuming it and stages exactly one
//! ciphertext-bound candidate. Phase two re-verifies and atomically consumes
//! both same-opening and FHDAR replay slots while advancing encrypted host
//! material, the HidingFri root, and sequence.
//!
//! This module imports no BFV secret key, decryption share, or plaintext reserve
//! opening. Initial public host material still needs creation evidence: matching
//! the embedded public key to the configured collective key does not prove that
//! its relinearization key and initial reserve ciphertexts were honestly
//! generated. Tier-1 issuers also see the private HidingFri/BFV openings; this
//! module verifies their authenticated receipt and does not rename it as ZK.

use std::fmt;

use deos_view::ViewNode;
use dregg_circuit_prove::dark_amm_private::RULE_ID as PRIVATE_AMM_RULE_ID;
use dreggnet_offerings::{
    Action, BinaryArtifactDescriptor, BinaryArtifactError, BinaryArtifactVisibility,
    BinaryOperationDescriptor, BinaryOperationError, BinaryOperationReceipt,
    BinaryOperationReplayMaterial, DreggIdentity, Offering, OfferingError, Outcome, RunCost,
    SessionConfig, Surface, VerifyReport,
};
use fhe::bfv::PublicKey;
use fhe_traits::{DeserializeParametrized, Serialize as FheSerialize};
use fhegg_fhe::amm_same_opening::{
    AmmPrivacyTier, AmmSameOpeningContext, canonical_bfv_parameters_digest,
};
use fhegg_fhe::attestation::{
    AuthenticatedQuorumVerifier, ComputationIntegrityVerifier, ReplayGuard, SnapshotReplayGuard,
};
use fhegg_fhe::dark_amm::{
    DarkPool, DarkPoolPublicHostMaterial, MAX_DARK_AMM_PUBLIC_HOST_MATERIAL_BYTES,
    PrivateAppliedSwap,
};
use fhegg_fhe::dark_amm_attested::{
    AttestedPrivateDecisionPolicy, commit_attested_private_decision_in_context,
};
use fhegg_fhe::decision_attestation::AttestedDecisionReceipt;
use fhegg_fhe::mpc_party::{DecisionTranscript, MAX_DECISION_TRANSCRIPT_BYTES};
use fhegg_fhe::threshold::{BfvParams, CollectivePublicKey, KeygenSession};

use crate::dark_amm_collective_worker::{
    CollectiveDecisionTask, CollectiveDecisionTaskContext, MAX_COLLECTIVE_DECISION_TASK_BYTES,
};
use crate::dark_amm_game::{
    DarkAmmPublicSession, MAX_DARK_AMM_REQUEST_BYTES, SameOpeningProvedEncryptedSwapRequest,
};

const CHECKPOINT_MAGIC: &[u8; 8] = b"DBACv001";
const CHECKPOINT_DOMAIN: &str = "dregg-dark-amm-collective-checkpoint-v1";
const REPLAY_CONTEXT_DOMAIN: &str = "dregg-dark-amm-collective-replay-context-v2";
const BABYBEAR_P: u32 = 2_013_265_921;
const MAX_REPLAY_WIRE_BYTES: usize = 40 * 1024 * 1024;
const MAX_CHECKPOINT_BYTES: usize = MAX_DARK_AMM_PUBLIC_HOST_MATERIAL_BYTES
    + MAX_DARK_AMM_REQUEST_BYTES
    + 2 * MAX_REPLAY_WIRE_BYTES
    + 1024;

const DECISION_BUNDLE_MAGIC: &[u8; 8] = b"DBCDv001";
const MAX_DECISION_RECEIPT_BYTES: usize = 16 * 1024 * 1024;
pub const MAX_COLLECTIVE_DECISION_BUNDLE_BYTES: usize =
    MAX_DECISION_TRANSCRIPT_BYTES + MAX_DECISION_RECEIPT_BYTES + 32;

pub const DARK_AMM_COLLECTIVE_STAGE_OPERATION: &str = "dark-amm.collective-stage.v1";
pub const DARK_AMM_COLLECTIVE_STAGE_MEDIA_TYPE: &str =
    "application/vnd.dregg.dark-amm-collective-stage.v1";
pub const DARK_AMM_COLLECTIVE_STAGE_DISCLOSURE: &str = "Stages one collective-key encrypted candidate after verifying its HidingFri transition and Tier-1 same-opening quorum. The public host learns no reserve or amount opening; configured Tier-1 issuers see the witness and encryption seeds. State does not advance until an independent FHDAR decision is committed.";

pub const DARK_AMM_COLLECTIVE_COMMIT_OPERATION: &str = "dark-amm.collective-commit.v1";
pub const DARK_AMM_COLLECTIVE_COMMIT_MEDIA_TYPE: &str =
    "application/vnd.dregg.dark-amm-collective-decision.v1";
pub const DARK_AMM_COLLECTIVE_COMMIT_DISCLOSURE: &str = "Commits the staged collective-key candidate only after a strict reveal-only equality transcript and independent authenticated FHDAR quorum receipt accept it. The bundle contains masked gate openings and one decision bit, never reserves, amounts, shares, operands, or a BFV secret key.";

/// Exact public candidate identity accepted by the abandon operation. Requiring
/// the current task digest makes a delayed cancellation fail closed after a
/// different candidate is staged at the same table.
pub const DARK_AMM_COLLECTIVE_ABANDON_OPERATION: &str = "dark-amm.collective-abandon.v1";
pub const DARK_AMM_COLLECTIVE_ABANDON_MEDIA_TYPE: &str =
    "application/vnd.dregg.dark-amm-collective-abandon.v1";
pub const DARK_AMM_COLLECTIVE_ABANDON_BYTES: usize = 32;
pub const DARK_AMM_COLLECTIVE_ABANDON_DISCLOSURE: &str = "Abandons exactly the currently staged collective-key candidate without consuming either authority replay slot or advancing encrypted pool/root/sequence state. The 32-byte body is the public decision-task digest; only the same frontend identity that staged the candidate may abandon it.";

/// Read-only work item exported after phase one for independent custodians.
pub const DARK_AMM_COLLECTIVE_TASK_ARTIFACT: &str = "dark-amm.collective-decision-task.v1";
pub const DARK_AMM_COLLECTIVE_TASK_MEDIA_TYPE: &str =
    "application/vnd.dregg.dark-amm-collective-decision-task.v1";
pub const DARK_AMM_COLLECTIVE_TASK_DISCLOSURE: &str = "Public collective-decision work item: exact encrypted candidate carrier plus hosted table/round/root, same-opening claim, committed material, BFV/DKG/key identity, and equality shape. It contains no plaintext reserve or amount, witness, encryption seed, secret key, decryption share, party-local mask, MPC operand, Beaver share, or authority signing key.";

/// Stable refusal surface for the public-only collective session.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CollectiveDarkAmmError {
    Malformed(String),
    Configuration(String),
    Refused(String),
    PendingCandidateExists,
    NoPendingCandidate,
    SequenceExhausted,
}

impl fmt::Display for CollectiveDarkAmmError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Malformed(reason) => write!(f, "malformed collective Dark AMM state: {reason}"),
            Self::Configuration(reason) => {
                write!(f, "invalid collective Dark AMM configuration: {reason}")
            }
            Self::Refused(reason) => write!(f, "collective Dark AMM request refused: {reason}"),
            Self::PendingCandidateExists => write!(f, "one encrypted candidate is already pending"),
            Self::NoPendingCandidate => write!(f, "no encrypted candidate is pending"),
            Self::SequenceExhausted => write!(f, "collective Dark AMM sequence is exhausted"),
        }
    }
}

impl std::error::Error for CollectiveDarkAmmError {}

/// Canonical phase-two object transported by web, Telegram, Discord, or a
/// native coordinator. Both members are public reveal-only artifacts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CollectiveDecisionBundle {
    transcript: DecisionTranscript,
    receipt: AttestedDecisionReceipt,
}

impl CollectiveDecisionBundle {
    pub fn new(transcript: DecisionTranscript, receipt: AttestedDecisionReceipt) -> Self {
        Self {
            transcript,
            receipt,
        }
    }

    pub fn transcript(&self) -> &DecisionTranscript {
        &self.transcript
    }

    pub fn receipt(&self) -> &AttestedDecisionReceipt {
        &self.receipt
    }

    pub fn to_wire_bytes(&self) -> Result<Vec<u8>, CollectiveDarkAmmError> {
        let transcript = self
            .transcript
            .to_wire_bytes()
            .map_err(|error| CollectiveDarkAmmError::Malformed(error.to_string()))?;
        let receipt = self
            .receipt
            .to_wire_bytes()
            .map_err(|error| CollectiveDarkAmmError::Malformed(error.to_string()))?;
        if receipt.len() > MAX_DECISION_RECEIPT_BYTES {
            return Err(CollectiveDarkAmmError::Malformed(
                "decision receipt exceeds the collective bundle limit".to_string(),
            ));
        }
        let total = DECISION_BUNDLE_MAGIC
            .len()
            .checked_add(16)
            .and_then(|len| len.checked_add(transcript.len()))
            .and_then(|len| len.checked_add(receipt.len()))
            .ok_or_else(|| {
                CollectiveDarkAmmError::Malformed("decision bundle length overflow".to_string())
            })?;
        if total > MAX_COLLECTIVE_DECISION_BUNDLE_BYTES {
            return Err(CollectiveDarkAmmError::Malformed(
                "decision bundle exceeds the allocation limit".to_string(),
            ));
        }
        let mut out = Vec::with_capacity(total);
        out.extend_from_slice(DECISION_BUNDLE_MAGIC);
        put_u64(&mut out, transcript.len() as u64);
        out.extend_from_slice(&transcript);
        put_u64(&mut out, receipt.len() as u64);
        out.extend_from_slice(&receipt);
        Ok(out)
    }

    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, CollectiveDarkAmmError> {
        if bytes.len() > MAX_COLLECTIVE_DECISION_BUNDLE_BYTES {
            return Err(CollectiveDarkAmmError::Malformed(
                "decision bundle exceeds the allocation limit".to_string(),
            ));
        }
        let mut input = DecisionBundleReader::new(bytes);
        if input.array::<8>()? != *DECISION_BUNDLE_MAGIC {
            return Err(CollectiveDarkAmmError::Malformed(
                "wrong collective decision bundle version".to_string(),
            ));
        }
        let transcript_wire = input.bytes(MAX_DECISION_TRANSCRIPT_BYTES)?;
        let receipt_wire = input.bytes(MAX_DECISION_RECEIPT_BYTES)?;
        input.finish()?;
        let transcript = DecisionTranscript::from_wire_bytes(transcript_wire)
            .map_err(|error| CollectiveDarkAmmError::Malformed(error.to_string()))?;
        let receipt = AttestedDecisionReceipt::from_wire_bytes(receipt_wire)
            .map_err(|error| CollectiveDarkAmmError::Malformed(error.to_string()))?;
        let bundle = Self {
            transcript,
            receipt,
        };
        if bundle.to_wire_bytes()? != bytes {
            return Err(CollectiveDarkAmmError::Malformed(
                "collective decision bundle is not canonical".to_string(),
            ));
        }
        Ok(bundle)
    }
}

/// Exact public relying-party configuration. The same-opening authority and
/// FHDAR decision verifier are independent policies even when a deployment
/// intentionally gives them overlapping rosters.
#[derive(Clone)]
pub struct CollectiveDarkAmmConfig {
    hosted_session: [u8; 32],
    params: BfvParams,
    keygen: KeygenSession,
    collective: CollectivePublicKey,
    same_opening_verifier: AuthenticatedQuorumVerifier,
    decision_policy: AttestedPrivateDecisionPolicy,
    same_opening_replay_context: [u8; 32],
    decision_replay_context: [u8; 32],
}

impl CollectiveDarkAmmConfig {
    pub fn new(
        hosted_session: [u8; 32],
        params: BfvParams,
        keygen: KeygenSession,
        collective: CollectivePublicKey,
        same_opening_verifier: AuthenticatedQuorumVerifier,
        decision_policy: AttestedPrivateDecisionPolicy,
    ) -> Result<Self, CollectiveDarkAmmError> {
        if hosted_session == [0; 32] {
            return Err(CollectiveDarkAmmError::Configuration(
                "hosted session must be nonzero".to_string(),
            ));
        }
        if keygen.n_parties() != decision_policy.n_parties() {
            return Err(CollectiveDarkAmmError::Configuration(format!(
                "DKG has {} parties but the decision circuit policy has {}",
                keygen.n_parties(),
                decision_policy.n_parties()
            )));
        }
        if params.plaintext_modulus() != decision_policy.plaintext_modulus() {
            return Err(CollectiveDarkAmmError::Configuration(
                "decision policy names a different BFV plaintext modulus".to_string(),
            ));
        }
        let collective_identity_digest = collective_identity_digest(&params, &keygen, &collective);
        let same_opening_replay_context = replay_context(
            b"same-opening",
            &hosted_session,
            &same_opening_verifier.verifier_id(),
            &collective_identity_digest,
        );
        let decision_replay_context = replay_context(
            b"fhdar-decision",
            &hosted_session,
            &decision_policy.verifier().verifier_id(),
            &collective_identity_digest,
        );
        Ok(Self {
            hosted_session,
            params,
            keygen,
            collective,
            same_opening_verifier,
            decision_policy,
            same_opening_replay_context,
            decision_replay_context,
        })
    }

    pub const fn hosted_session(&self) -> [u8; 32] {
        self.hosted_session
    }

    pub fn params(&self) -> &BfvParams {
        &self.params
    }

    pub fn keygen(&self) -> &KeygenSession {
        &self.keygen
    }

    pub fn collective(&self) -> &CollectivePublicKey {
        &self.collective
    }

    pub fn same_opening_verifier(&self) -> &AuthenticatedQuorumVerifier {
        &self.same_opening_verifier
    }

    pub fn decision_policy(&self) -> &AttestedPrivateDecisionPolicy {
        &self.decision_policy
    }

    fn public_key_digest(&self) -> [u8; 32] {
        *blake3::hash(&self.collective.pk.to_bytes()).as_bytes()
    }

    fn validate_material(
        &self,
        material: &DarkPoolPublicHostMaterial,
    ) -> Result<(), CollectiveDarkAmmError> {
        DarkPool::restore_public_host(self.params.arc(), material)
            .map_err(|error| CollectiveDarkAmmError::Configuration(error.to_string()))?;
        if material.public_key_bytes() != self.collective.pk.to_bytes() {
            return Err(CollectiveDarkAmmError::Configuration(
                "public host material is not under the configured collective key".to_string(),
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PendingCandidate {
    request_wire: Vec<u8>,
    same_opening_claim_digest: [u8; 32],
    candidate_nonce: [u8; 32],
}

/// Public result of phase one. It names the candidate without carrying a
/// ciphertext, witness, reserve, or amount opening.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StagedCollectiveSwap {
    pub sequence: u64,
    pub new_root: [u32; 8],
    pub same_opening_claim_digest: [u8; 32],
    pub candidate_nonce: [u8; 32],
    /// Contextual worker-task digest used as the PartyMPC/FHDAR session nonce.
    pub decision_task_digest: [u8; 32],
}

/// Public result of the atomic FHDAR commit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CommittedCollectiveSwap {
    pub committed_sequence: u64,
    pub next_sequence: u64,
    pub new_root: [u32; 8],
    pub public_host_material_digest: [u8; 32],
    /// Tier-1 authority claim that bound HidingFri and BFV openings.
    pub same_opening_claim_digest: [u8; 32],
    /// Independent FHDAR authority claim that accepted the candidate.
    pub decision_claim_digest: [u8; 32],
}

/// Secretless host state. The optional pending carrier contains only the
/// canonical v3 request and public digests/nonces needed to reconstruct it.
#[derive(Clone)]
pub struct CollectiveDarkAmmSession {
    config: CollectiveDarkAmmConfig,
    public_host_material: DarkPoolPublicHostMaterial,
    current_root: [u32; 8],
    next_sequence: u64,
    same_opening_replay: SnapshotReplayGuard,
    decision_replay: SnapshotReplayGuard,
    pending: Option<PendingCandidate>,
}

impl CollectiveDarkAmmSession {
    pub fn new(
        config: CollectiveDarkAmmConfig,
        public_host_material: DarkPoolPublicHostMaterial,
        current_root: [u32; 8],
        next_sequence: u64,
    ) -> Result<Self, CollectiveDarkAmmError> {
        validate_root(current_root)?;
        config.validate_material(&public_host_material)?;
        let same_opening_replay = SnapshotReplayGuard::new(config.same_opening_replay_context);
        let decision_replay = SnapshotReplayGuard::new(config.decision_replay_context);
        let session = Self {
            config,
            public_host_material,
            current_root,
            next_sequence,
            same_opening_replay,
            decision_replay,
            pending: None,
        };
        session.public_session()?;
        Ok(session)
    }

    pub const fn current_root(&self) -> [u32; 8] {
        self.current_root
    }

    pub const fn next_sequence(&self) -> u64 {
        self.next_sequence
    }

    pub fn has_pending_candidate(&self) -> bool {
        self.pending.is_some()
    }

    pub fn same_opening_replay_revision(&self) -> u64 {
        self.same_opening_replay.revision()
    }

    pub fn decision_replay_revision(&self) -> u64 {
        self.decision_replay.revision()
    }

    pub fn public_host_material(&self) -> &DarkPoolPublicHostMaterial {
        &self.public_host_material
    }

    /// Reconstruct the encrypted invariant target for the currently staged
    /// candidate. This is the public worker handoff: it contains ciphertexts
    /// and public bounds only, never the reserves, amounts, witness, opening
    /// seeds, a BFV secret key, or a threshold decryption share.
    ///
    /// The commit path independently reconstructs and re-verifies the same
    /// candidate before accepting a decision, so a worker cannot substitute a
    /// different ciphertext by mutating this returned value.
    pub fn pending_decision_candidate(&self) -> Result<PrivateAppliedSwap, CollectiveDarkAmmError> {
        let pending = self
            .pending
            .as_ref()
            .ok_or(CollectiveDarkAmmError::NoPendingCandidate)?;
        let request = decode_request(&pending.request_wire)?;
        self.validate_request_bindings(&request)?;
        let candidate = self.reconstruct_candidate(&request)?;
        if candidate.decision_session_nonce() != pending.candidate_nonce {
            return Err(CollectiveDarkAmmError::Refused(
                "pending candidate no longer reconstructs against the committed pre-state"
                    .to_string(),
            ));
        }
        Ok(candidate)
    }

    /// Canonical public work order for the currently staged candidate.
    ///
    /// Unlike [`pending_decision_candidate`](Self::pending_decision_candidate),
    /// this is safe to transport to a separately configured worker: the task
    /// binds the table/round/root, same-opening authority claim, public
    /// BFV/DKG identity, committed material, equality width, and the exact
    /// encrypted candidate carrier. Its digest—not the context-free candidate
    /// nonce—is the PartyMPC/FHDAR session nonce.
    pub fn pending_decision_task(&self) -> Result<CollectiveDecisionTask, CollectiveDarkAmmError> {
        let pending = self
            .pending
            .as_ref()
            .ok_or(CollectiveDarkAmmError::NoPendingCandidate)?;
        let candidate = self.pending_decision_candidate()?;
        self.decision_task_for(&candidate, pending.same_opening_claim_digest)
    }

    /// Deliberately abandon a staged candidate. Phase one has not consumed the
    /// same-opening replay slot, so the request or a same-sequence replacement
    /// may be staged after restart. All committed pool/root/sequence and both
    /// replay guards remain untouched.
    pub fn abandon_pending(&mut self) -> Result<StagedCollectiveSwap, CollectiveDarkAmmError> {
        let pending = self
            .pending
            .as_ref()
            .ok_or(CollectiveDarkAmmError::NoPendingCandidate)?;
        let request = decode_request(&pending.request_wire)?;
        let decision_task_digest =
            self.pending_decision_task()?
                .attestation_nonce()
                .map_err(|error| {
                    CollectiveDarkAmmError::Refused(format!("decision task refused: {error}"))
                })?;
        let abandoned = StagedCollectiveSwap {
            sequence: self.next_sequence,
            new_root: request.proved_request().statement().new_root,
            same_opening_claim_digest: pending.same_opening_claim_digest,
            candidate_nonce: pending.candidate_nonce,
            decision_task_digest,
        };
        self.pending = None;
        Ok(abandoned)
    }

    /// Producer view for the current root/sequence under the real collective
    /// key and public DKG identity.
    pub fn public_session(&self) -> Result<DarkAmmPublicSession, CollectiveDarkAmmError> {
        DarkAmmPublicSession::try_from_collective(
            self.config.hosted_session,
            &self.config.params,
            &self.config.keygen,
            &self.config.collective,
            self.public_host_material.k(),
            self.public_host_material.cap_x(),
            self.public_host_material.cap_y(),
            self.next_sequence,
            self.current_root,
        )
        .map_err(|error| CollectiveDarkAmmError::Configuration(error.to_string()))
    }

    /// Phase one: fully verify the collective Tier-1 receipt and stage exactly
    /// one encrypted candidate. No pool/root/sequence mutation occurs here.
    pub fn stage_same_opening_request(
        &mut self,
        request_wire: &[u8],
    ) -> Result<StagedCollectiveSwap, CollectiveDarkAmmError> {
        if self.pending.is_some() {
            return Err(CollectiveDarkAmmError::PendingCandidateExists);
        }
        let request = decode_request(request_wire)?;
        let mut replay_probe = self.same_opening_replay.clone();
        let (candidate, claim_digest) = self.verify_and_reconstruct(&request, &mut replay_probe)?;
        let candidate_nonce = candidate.decision_session_nonce();
        let decision_task_digest = self
            .decision_task_for(&candidate, claim_digest)?
            .attestation_nonce()
            .map_err(|error| {
                CollectiveDarkAmmError::Refused(format!("decision task refused: {error}"))
            })?;
        let staged = StagedCollectiveSwap {
            sequence: self.next_sequence,
            new_root: request.proved_request().statement().new_root,
            same_opening_claim_digest: claim_digest,
            candidate_nonce,
            decision_task_digest,
        };
        self.pending = Some(PendingCandidate {
            request_wire: request_wire.to_vec(),
            same_opening_claim_digest: claim_digest,
            candidate_nonce,
        });
        Ok(staged)
    }

    /// Phase two: verify an independently configured FHDAR decision against a
    /// freshly reconstructed candidate and commit into a detached pool. Every
    /// fallible step finishes before the authoritative fields are replaced.
    pub fn commit_attested_decision(
        &mut self,
        transcript: &DecisionTranscript,
        receipt: &AttestedDecisionReceipt,
    ) -> Result<CommittedCollectiveSwap, CollectiveDarkAmmError> {
        let pending = self
            .pending
            .as_ref()
            .ok_or(CollectiveDarkAmmError::NoPendingCandidate)?;
        let request = decode_request(&pending.request_wire)?;
        self.validate_request_bindings(&request)?;
        let mut staged_same_opening_replay = self.same_opening_replay.clone();
        let (candidate, reverified_claim_digest) =
            self.verify_and_reconstruct(&request, &mut staged_same_opening_replay)?;
        if candidate.decision_session_nonce() != pending.candidate_nonce
            || reverified_claim_digest != pending.same_opening_claim_digest
        {
            return Err(CollectiveDarkAmmError::Refused(
                "pending candidate no longer matches its Tier-1 authority claim".to_string(),
            ));
        }
        let mut detached_pool =
            DarkPool::restore_public_host(self.config.params.arc(), &self.public_host_material)
                .map_err(|error| CollectiveDarkAmmError::Refused(error.to_string()))?;
        let task = self.decision_task_for(&candidate, reverified_claim_digest)?;
        if !task.matches_candidate(&candidate) {
            return Err(CollectiveDarkAmmError::Refused(
                "reconstructed decision task does not match the authoritative candidate"
                    .to_string(),
            ));
        }
        let decision_session_nonce = task.attestation_nonce().map_err(|error| {
            CollectiveDarkAmmError::Refused(format!("decision task refused: {error}"))
        })?;
        let mut staged_replay = self.decision_replay.clone();
        commit_attested_private_decision_in_context(
            &mut detached_pool,
            &candidate,
            decision_session_nonce,
            &self.config.decision_policy,
            transcript,
            receipt,
            &mut staged_replay,
        )
        .map_err(|error| CollectiveDarkAmmError::Refused(error.to_string()))?;
        let next_material = detached_pool
            .public_host_material()
            .map_err(|error| CollectiveDarkAmmError::Refused(error.to_string()))?;
        let committed_sequence = self.next_sequence;
        let next_sequence = committed_sequence
            .checked_add(1)
            .ok_or(CollectiveDarkAmmError::SequenceExhausted)?;
        let new_root = request.proved_request().statement().new_root;
        let public_host_material_digest = next_material.material_digest();
        let same_opening_claim_digest = pending.same_opening_claim_digest;
        let decision_claim_digest = receipt.claim_digest();

        // Atomic authoritative replacement: all parsing, FHE, FHDAR, replay,
        // serialization, and sequence checks above operated on detached state.
        self.public_host_material = next_material;
        self.current_root = new_root;
        self.next_sequence = next_sequence;
        self.same_opening_replay = staged_same_opening_replay;
        self.decision_replay = staged_replay;
        self.pending = None;

        Ok(CommittedCollectiveSwap {
            committed_sequence,
            next_sequence,
            new_root,
            public_host_material_digest,
            same_opening_claim_digest,
            decision_claim_digest,
        })
    }

    /// Strict public restart carrier. Persist this in the same transaction as
    /// an accepted stage or commit. Its checksum detects corruption, not
    /// rollback; production storage still needs a monotonic/consensus anchor.
    pub fn checkpoint_wire_bytes(&self) -> Vec<u8> {
        let material = self.public_host_material.to_wire_bytes();
        let same_replay = self.same_opening_replay.to_wire_bytes();
        let decision_replay = self.decision_replay.to_wire_bytes();
        let mut out = Vec::new();
        out.extend_from_slice(CHECKPOINT_MAGIC);
        out.extend_from_slice(&self.config.hosted_session);
        for lane in self.current_root {
            out.extend_from_slice(&lane.to_le_bytes());
        }
        put_u64(&mut out, self.next_sequence);
        put_bytes(&mut out, &material);
        put_bytes(&mut out, &same_replay);
        put_bytes(&mut out, &decision_replay);
        match &self.pending {
            None => out.push(0),
            Some(pending) => {
                out.push(1);
                put_bytes(&mut out, &pending.request_wire);
                out.extend_from_slice(&pending.same_opening_claim_digest);
                out.extend_from_slice(&pending.candidate_nonce);
            }
        }
        let checksum = checkpoint_checksum(&out);
        out.extend_from_slice(&checksum);
        out
    }

    /// Restore committed material, both replay sets, and—when present—the
    /// strict public pending carrier. Pending restoration re-verifies the full
    /// proof/signatures against a clone of the durable replay guard and thus
    /// requires its sequence slot to remain fresh until phase two commits.
    pub fn restore_from_checkpoint(
        config: CollectiveDarkAmmConfig,
        bytes: &[u8],
    ) -> Result<Self, CollectiveDarkAmmError> {
        let decoded = DecodedCheckpoint::parse(bytes)?;
        if decoded.hosted_session != config.hosted_session {
            return Err(CollectiveDarkAmmError::Configuration(
                "checkpoint names a different hosted session".to_string(),
            ));
        }
        validate_root(decoded.current_root)?;
        let material =
            DarkPoolPublicHostMaterial::from_wire_bytes(decoded.material_wire, config.params.arc())
                .map_err(|error| CollectiveDarkAmmError::Malformed(error.to_string()))?;
        config.validate_material(&material)?;
        let same_opening_replay = SnapshotReplayGuard::from_wire_bytes(
            config.same_opening_replay_context,
            decoded.same_opening_replay_wire,
        )
        .map_err(|error| CollectiveDarkAmmError::Malformed(error.to_string()))?;
        let decision_replay = SnapshotReplayGuard::from_wire_bytes(
            config.decision_replay_context,
            decoded.decision_replay_wire,
        )
        .map_err(|error| CollectiveDarkAmmError::Malformed(error.to_string()))?;
        let pending = decoded.pending.map(|pending| PendingCandidate {
            request_wire: pending.request_wire.to_vec(),
            same_opening_claim_digest: pending.same_opening_claim_digest,
            candidate_nonce: pending.candidate_nonce,
        });
        let session = Self {
            config,
            public_host_material: material,
            current_root: decoded.current_root,
            next_sequence: decoded.next_sequence,
            same_opening_replay,
            decision_replay,
            pending,
        };
        session.public_session()?;
        if let Some(pending) = &session.pending {
            let request = decode_request(&pending.request_wire)?;
            let mut replay_probe = session.same_opening_replay.clone();
            let (candidate, claim_digest) =
                session.verify_and_reconstruct(&request, &mut replay_probe)?;
            if candidate.decision_session_nonce() != pending.candidate_nonce
                || claim_digest != pending.same_opening_claim_digest
            {
                return Err(CollectiveDarkAmmError::Malformed(
                    "pending carrier digests do not reconstruct".to_string(),
                ));
            }
        }
        if session.checkpoint_wire_bytes() != bytes {
            return Err(CollectiveDarkAmmError::Malformed(
                "checkpoint is not canonically encoded".to_string(),
            ));
        }
        Ok(session)
    }

    fn verify_and_reconstruct<R: ReplayGuard>(
        &self,
        request: &SameOpeningProvedEncryptedSwapRequest,
        replay: &mut R,
    ) -> Result<(PrivateAppliedSwap, [u8; 32]), CollectiveDarkAmmError> {
        self.validate_request_bindings(request)?;
        let proved = request.proved_request();
        let (dx, dy) = proved
            .bounded_ciphertexts(self.config.params.arc())
            .map_err(|error| CollectiveDarkAmmError::Refused(error.to_string()))?;
        let proof = proved
            .decoded_private_amm_proof()
            .map_err(|error| CollectiveDarkAmmError::Refused(error.to_string()))?;
        let context = AmmSameOpeningContext {
            privacy_tier: AmmPrivacyTier::Tier1IssuerVisible,
            hosted_session: self.config.hosted_session,
            sequence: self.next_sequence,
            dx_bound: proved.dx_bound(),
            dy_bound: proved.dy_bound(),
            params: &self.config.params,
            keygen: &self.config.keygen,
            collective: &self.config.collective,
            dx_ciphertext: &dx.ct,
            dy_ciphertext: &dy.ct,
            proof: &proof,
            statement: proved.statement(),
        };
        let verified = request
            .same_opening_receipt()
            .verify(&context, &self.config.same_opening_verifier, replay)
            .map_err(|error| {
                CollectiveDarkAmmError::Refused(format!(
                    "collective Tier-1 same-opening verification failed: {error}"
                ))
            })?;
        let candidate = self.reconstruct_candidate(request)?;
        Ok((candidate, verified.claim_digest()))
    }

    fn reconstruct_candidate(
        &self,
        request: &SameOpeningProvedEncryptedSwapRequest,
    ) -> Result<PrivateAppliedSwap, CollectiveDarkAmmError> {
        let (dx, dy) = request
            .proved_request()
            .bounded_ciphertexts(self.config.params.arc())
            .map_err(|error| CollectiveDarkAmmError::Refused(error.to_string()))?;
        let pool =
            DarkPool::restore_public_host(self.config.params.arc(), &self.public_host_material)
                .map_err(|error| CollectiveDarkAmmError::Refused(error.to_string()))?;
        pool.try_private_swap_proposed(&dx, &dy)
            .map_err(|error| CollectiveDarkAmmError::Refused(error.to_string()))
    }

    fn decision_task_for(
        &self,
        candidate: &PrivateAppliedSwap,
        same_opening_claim_digest: [u8; 32],
    ) -> Result<CollectiveDecisionTask, CollectiveDarkAmmError> {
        let context = CollectiveDecisionTaskContext {
            hosted_session: self.config.hosted_session,
            sequence: self.next_sequence,
            committed_root: self.current_root,
            same_opening_claim_digest,
        };
        CollectiveDecisionTask::from_candidate(
            context,
            &self.public_host_material,
            &self.config.params,
            &self.config.keygen,
            &self.config.collective,
            self.config.decision_policy.value_bits(),
            candidate,
        )
        .map_err(|error| CollectiveDarkAmmError::Refused(format!("decision task refused: {error}")))
    }

    fn validate_request_bindings(
        &self,
        request: &SameOpeningProvedEncryptedSwapRequest,
    ) -> Result<(), CollectiveDarkAmmError> {
        let proved = request.proved_request();
        if proved.hosted_session() != self.config.hosted_session {
            return Err(CollectiveDarkAmmError::Refused(
                "request names a different hosted session".to_string(),
            ));
        }
        if proved.public_key_digest() != self.config.public_key_digest() {
            return Err(CollectiveDarkAmmError::Refused(
                "request names a different collective public key".to_string(),
            ));
        }
        if proved.sequence() != self.next_sequence {
            return Err(CollectiveDarkAmmError::Refused(format!(
                "request sequence {} is stale or skipped; expected {}",
                proved.sequence(),
                self.next_sequence
            )));
        }
        let statement = proved.statement();
        let public = self.public_session()?;
        let proof_context = public.proof_context().ok_or_else(|| {
            CollectiveDarkAmmError::Configuration(
                "collective public session unexpectedly lacks a proof context".to_string(),
            )
        })?;
        if statement.session != proof_context.receipt_session()
            || statement.rule != proof_context.rule()
            || statement.rule != PRIVATE_AMM_RULE_ID
            || u64::from(statement.k) != self.public_host_material.k()
            || statement.old_root != self.current_root
        {
            return Err(CollectiveDarkAmmError::Refused(
                "HidingFri statement does not name the exact session/rule/k/current root"
                    .to_string(),
            ));
        }
        validate_root(statement.new_root)?;
        Ok(())
    }
}

/// Reusable game-engine registration for collective-key Dark Bazaar tables.
/// Each offering session derives a distinct hosted-session domain from its
/// seed, while sharing only the deployment's public DKG/relinearization
/// material and authority policies.
#[derive(Clone)]
pub struct CollectiveDarkAmmOffering {
    base_hosted_session: [u8; 32],
    session_seed: u64,
    params: BfvParams,
    keygen: KeygenSession,
    collective: CollectivePublicKey,
    initial_material: DarkPoolPublicHostMaterial,
    initial_root: [u32; 8],
    same_opening_verifier: AuthenticatedQuorumVerifier,
    decision_policy: AttestedPrivateDecisionPolicy,
}

impl CollectiveDarkAmmOffering {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        base_hosted_session: [u8; 32],
        session_seed: u64,
        params: BfvParams,
        keygen: KeygenSession,
        collective: CollectivePublicKey,
        initial_material: DarkPoolPublicHostMaterial,
        initial_root: [u32; 8],
        same_opening_verifier: AuthenticatedQuorumVerifier,
        decision_policy: AttestedPrivateDecisionPolicy,
    ) -> Result<Self, CollectiveDarkAmmError> {
        if base_hosted_session == [0; 32] {
            return Err(CollectiveDarkAmmError::Configuration(
                "base hosted-session domain must be nonzero".to_string(),
            ));
        }
        validate_root(initial_root)?;
        let offering = Self {
            base_hosted_session,
            session_seed,
            params,
            keygen,
            collective,
            initial_material,
            initial_root,
            same_opening_verifier,
            decision_policy,
        };
        let config = offering.config_for_seed(session_seed)?;
        config.validate_material(&offering.initial_material)?;
        Ok(offering)
    }

    #[allow(clippy::too_many_arguments)]
    pub fn from_public_material(
        base_hosted_session: [u8; 32],
        session_seed: u64,
        params: BfvParams,
        keygen: KeygenSession,
        initial_material: DarkPoolPublicHostMaterial,
        initial_root: [u32; 8],
        same_opening_verifier: AuthenticatedQuorumVerifier,
        decision_policy: AttestedPrivateDecisionPolicy,
    ) -> Result<Self, CollectiveDarkAmmError> {
        let public_key = PublicKey::from_bytes(initial_material.public_key_bytes(), params.arc())
            .map_err(|error| {
            CollectiveDarkAmmError::Configuration(format!(
                "collective public key decode failed: {error}"
            ))
        })?;
        if public_key.to_bytes() != initial_material.public_key_bytes() {
            return Err(CollectiveDarkAmmError::Configuration(
                "collective public key is not canonically encoded".to_string(),
            ));
        }
        Self::new(
            base_hosted_session,
            session_seed,
            params,
            keygen,
            CollectivePublicKey { pk: public_key },
            initial_material,
            initial_root,
            same_opening_verifier,
            decision_policy,
        )
    }

    pub fn public_session_for_seed(
        &self,
        seed: u64,
    ) -> Result<DarkAmmPublicSession, CollectiveDarkAmmError> {
        if seed != self.session_seed {
            return Err(CollectiveDarkAmmError::Configuration(format!(
                "collective table is pinned to session seed {}, got {seed}",
                self.session_seed
            )));
        }
        self.open_collective(seed)?.public_session()
    }

    pub fn derive_hosted_session(
        base_hosted_session: [u8; 32],
        seed: u64,
        initial_material: &DarkPoolPublicHostMaterial,
    ) -> Result<[u8; 32], CollectiveDarkAmmError> {
        if base_hosted_session == [0; 32] {
            return Err(CollectiveDarkAmmError::Configuration(
                "base hosted-session domain must be nonzero".to_string(),
            ));
        }
        let mut hash =
            blake3::Hasher::new_derive_key("dregg-dark-amm-collective-offering-session-v1");
        hash.update(&base_hosted_session);
        hash.update(&seed.to_le_bytes());
        hash.update(&initial_material.material_digest());
        let mut hosted_session = *hash.finalize().as_bytes();
        if hosted_session == [0; 32] {
            hosted_session[0] = 1;
        }
        Ok(hosted_session)
    }

    fn hosted_session_for_seed(&self, seed: u64) -> [u8; 32] {
        Self::derive_hosted_session(self.base_hosted_session, seed, &self.initial_material)
            .expect("constructor validated the nonzero base hosted-session domain")
    }

    fn config_for_seed(
        &self,
        seed: u64,
    ) -> Result<CollectiveDarkAmmConfig, CollectiveDarkAmmError> {
        CollectiveDarkAmmConfig::new(
            self.hosted_session_for_seed(seed),
            self.params.clone(),
            self.keygen.clone(),
            self.collective.clone(),
            self.same_opening_verifier.clone(),
            self.decision_policy.clone(),
        )
    }

    fn open_collective(
        &self,
        seed: u64,
    ) -> Result<CollectiveDarkAmmSession, CollectiveDarkAmmError> {
        if seed != self.session_seed {
            return Err(CollectiveDarkAmmError::Configuration(format!(
                "collective table is pinned to session seed {}, got {seed}",
                self.session_seed
            )));
        }
        CollectiveDarkAmmSession::new(
            self.config_for_seed(seed)?,
            self.initial_material.clone(),
            self.initial_root,
            0,
        )
    }

    fn execute_stage(
        &self,
        session: &mut CollectiveDarkAmmGameSession,
        payload: &[u8],
        actor: &DreggIdentity,
    ) -> Result<BinaryOperationReceipt, BinaryOperationError> {
        if session.pending_actor.is_some() {
            return Err(BinaryOperationError::Refused(
                "collective staging slot already has a frontend owner".to_string(),
            ));
        }
        let staged = session
            .collective
            .stage_same_opening_request(payload)
            .map_err(map_collective_operation_error)?;
        let request_digest = *blake3::hash(payload).as_bytes();
        let public = session
            .collective
            .public_session()
            .map_err(map_collective_operation_error)?;
        let mut receipt =
            blake3::Hasher::new_derive_key("dregg-dark-amm-collective-stage-operation-receipt-v1");
        receipt.update(&public.session_id());
        receipt.update(&staged.sequence.to_le_bytes());
        receipt.update(&request_digest);
        receipt.update(&staged.same_opening_claim_digest);
        receipt.update(&staged.candidate_nonce);
        receipt.update(&staged.decision_task_digest);
        bind_actor(&mut receipt, actor)?;
        let receipt_id = *receipt.finalize().as_bytes();
        session.pending_actor = Some(actor.clone());
        Ok(BinaryOperationReceipt {
            operation: DARK_AMM_COLLECTIVE_STAGE_OPERATION.to_string(),
            receipt_id,
            public_fields: vec![
                (
                    "phase".to_string(),
                    "awaiting-authority-decision".to_string(),
                ),
                ("sequence".to_string(), staged.sequence.to_string()),
                ("newRoot".to_string(), hex_root(&staged.new_root)),
                (
                    "candidateNonce".to_string(),
                    hex_digest(&staged.candidate_nonce),
                ),
                (
                    "decisionTaskDigest".to_string(),
                    hex_digest(&staged.decision_task_digest),
                ),
                (
                    "sameOpeningClaimDigest".to_string(),
                    hex_digest(&staged.same_opening_claim_digest),
                ),
                ("requestDigest".to_string(), hex_digest(&request_digest)),
                (
                    "collectiveParties".to_string(),
                    session.collective.config.keygen.n_parties().to_string(),
                ),
            ],
        })
    }

    fn execute_commit(
        &self,
        session: &mut CollectiveDarkAmmGameSession,
        payload: &[u8],
        actor: &DreggIdentity,
    ) -> Result<BinaryOperationReceipt, BinaryOperationError> {
        require_pending_actor(session, actor)?;
        let bundle = CollectiveDecisionBundle::from_wire_bytes(payload)
            .map_err(map_collective_operation_error)?;
        let committed = session
            .collective
            .commit_attested_decision(bundle.transcript(), bundle.receipt())
            .map_err(map_collective_operation_error)?;
        let bundle_digest = *blake3::hash(payload).as_bytes();
        let public = session
            .collective
            .public_session()
            .map_err(map_collective_operation_error)?;
        let mut receipt =
            blake3::Hasher::new_derive_key("dregg-dark-amm-collective-commit-operation-receipt-v1");
        receipt.update(&public.session_id());
        receipt.update(&committed.committed_sequence.to_le_bytes());
        receipt.update(&bundle_digest);
        receipt.update(&committed.public_host_material_digest);
        receipt.update(&committed.same_opening_claim_digest);
        receipt.update(&committed.decision_claim_digest);
        bind_actor(&mut receipt, actor)?;
        let receipt_id = *receipt.finalize().as_bytes();
        session.pending_actor = None;
        Ok(BinaryOperationReceipt {
            operation: DARK_AMM_COLLECTIVE_COMMIT_OPERATION.to_string(),
            receipt_id,
            public_fields: vec![
                ("phase".to_string(), "committed".to_string()),
                (
                    "committedSequence".to_string(),
                    committed.committed_sequence.to_string(),
                ),
                (
                    "nextSequence".to_string(),
                    committed.next_sequence.to_string(),
                ),
                ("newRoot".to_string(), hex_root(&committed.new_root)),
                (
                    "publicHostMaterialDigest".to_string(),
                    hex_digest(&committed.public_host_material_digest),
                ),
                (
                    "sameOpeningClaimDigest".to_string(),
                    hex_digest(&committed.same_opening_claim_digest),
                ),
                (
                    "decisionClaimDigest".to_string(),
                    hex_digest(&committed.decision_claim_digest),
                ),
                (
                    "decisionBundleDigest".to_string(),
                    hex_digest(&bundle_digest),
                ),
                (
                    "decisionThreshold".to_string(),
                    session
                        .collective
                        .config
                        .decision_policy
                        .verifier()
                        .threshold()
                        .to_string(),
                ),
            ],
        })
    }

    fn execute_abandon(
        &self,
        session: &mut CollectiveDarkAmmGameSession,
        payload: &[u8],
        actor: &DreggIdentity,
    ) -> Result<BinaryOperationReceipt, BinaryOperationError> {
        require_pending_actor(session, actor)?;
        let presented_task_digest = decode_abandon_digest(payload)?;
        let expected_task_digest = session
            .collective
            .pending_decision_task()
            .and_then(|task| {
                task.attestation_nonce().map_err(|error| {
                    CollectiveDarkAmmError::Refused(format!("decision task refused: {error}"))
                })
            })
            .map_err(map_collective_operation_error)?;
        if presented_task_digest != expected_task_digest {
            return Err(BinaryOperationError::Refused(
                "abandon request names a different pending decision task".to_string(),
            ));
        }
        let abandoned = session
            .collective
            .abandon_pending()
            .map_err(map_collective_operation_error)?;
        let public = session
            .collective
            .public_session()
            .map_err(map_collective_operation_error)?;
        let mut receipt =
            blake3::Hasher::new_derive_key("dregg-dark-amm-collective-abandon-receipt-v1");
        receipt.update(&public.session_id());
        receipt.update(&abandoned.sequence.to_le_bytes());
        for lane in abandoned.new_root {
            receipt.update(&lane.to_le_bytes());
        }
        receipt.update(&abandoned.same_opening_claim_digest);
        receipt.update(&abandoned.candidate_nonce);
        receipt.update(&abandoned.decision_task_digest);
        bind_actor(&mut receipt, actor)?;
        let receipt_id = *receipt.finalize().as_bytes();
        session.pending_actor = None;
        Ok(BinaryOperationReceipt {
            operation: DARK_AMM_COLLECTIVE_ABANDON_OPERATION.to_string(),
            receipt_id,
            public_fields: vec![
                ("phase".to_string(), "abandoned".to_string()),
                ("sequence".to_string(), abandoned.sequence.to_string()),
                ("newRoot".to_string(), hex_root(&abandoned.new_root)),
                (
                    "candidateNonce".to_string(),
                    hex_digest(&abandoned.candidate_nonce),
                ),
                (
                    "decisionTaskDigest".to_string(),
                    hex_digest(&abandoned.decision_task_digest),
                ),
                (
                    "sameOpeningClaimDigest".to_string(),
                    hex_digest(&abandoned.same_opening_claim_digest),
                ),
                ("replaySlotsConsumed".to_string(), "0".to_string()),
            ],
        })
    }
}

#[derive(Clone)]
struct AcceptedCollectiveOperation {
    operation: &'static str,
    canonical_payload: Vec<u8>,
    actor: DreggIdentity,
    receipt: BinaryOperationReceipt,
}

/// Public-only hosted game state. The authoritative encrypted pool and replay
/// cursors live in `collective`; `accepted` is the replay-verification history
/// and contains only canonical public protocol objects.
pub struct CollectiveDarkAmmGameSession {
    seed: u64,
    collective: CollectiveDarkAmmSession,
    /// Frontend identity that staged the live candidate. The cryptographic
    /// authorities remain independent; this is the shared-surface ownership
    /// gate that prevents one player from committing or cancelling another
    /// player's pending operation. Host replay reconstructs it from the
    /// actor-bearing operation journal rather than trusting a state snapshot.
    pending_actor: Option<DreggIdentity>,
    accepted: Vec<AcceptedCollectiveOperation>,
}

impl CollectiveDarkAmmGameSession {
    pub fn public_session(&self) -> Result<DarkAmmPublicSession, CollectiveDarkAmmError> {
        self.collective.public_session()
    }

    pub fn has_pending_candidate(&self) -> bool {
        self.collective.has_pending_candidate()
    }

    /// Public encrypted target for an in-process or separately transported
    /// collective decision worker. See
    /// [`CollectiveDarkAmmSession::pending_decision_candidate`].
    pub fn pending_decision_candidate(&self) -> Result<PrivateAppliedSwap, CollectiveDarkAmmError> {
        self.collective.pending_decision_candidate()
    }

    /// Strict public work order for an external collective decision worker.
    pub fn pending_decision_task(&self) -> Result<CollectiveDecisionTask, CollectiveDarkAmmError> {
        self.collective.pending_decision_task()
    }

    pub fn committed_swaps(&self) -> u64 {
        self.collective.next_sequence()
    }
}

impl Offering for CollectiveDarkAmmOffering {
    type Session = CollectiveDarkAmmGameSession;

    fn open(&self, cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        let seed = cfg.seed.unwrap_or(1);
        let collective = self
            .open_collective(seed)
            .map_err(|error| OfferingError::Deploy(error.to_string()))?;
        Ok(CollectiveDarkAmmGameSession {
            seed,
            collective,
            pending_actor: None,
            accepted: Vec::new(),
        })
    }

    fn actions(&self, _session: &Self::Session) -> Vec<Action> {
        Vec::new()
    }

    fn advance(
        &self,
        _session: &mut Self::Session,
        _input: Action,
        _actor: DreggIdentity,
    ) -> Outcome {
        Outcome::Refused(
            "the collective Dark Pool advances only through its staged binary operations"
                .to_string(),
        )
    }

    fn verify(&self, session: &Self::Session) -> VerifyReport {
        let mut replay = match self.open_collective(session.seed) {
            Ok(collective) => CollectiveDarkAmmGameSession {
                seed: session.seed,
                collective,
                pending_actor: None,
                accepted: Vec::new(),
            },
            Err(error) => return VerifyReport::broken(0, error.to_string()),
        };
        for (index, accepted) in session.accepted.iter().enumerate() {
            let result = match accepted.operation {
                DARK_AMM_COLLECTIVE_STAGE_OPERATION => {
                    self.execute_stage(&mut replay, &accepted.canonical_payload, &accepted.actor)
                }
                DARK_AMM_COLLECTIVE_COMMIT_OPERATION => {
                    self.execute_commit(&mut replay, &accepted.canonical_payload, &accepted.actor)
                }
                DARK_AMM_COLLECTIVE_ABANDON_OPERATION => {
                    self.execute_abandon(&mut replay, &accepted.canonical_payload, &accepted.actor)
                }
                other => Err(BinaryOperationError::UnknownOperation(other.to_string())),
            };
            match result {
                Ok(receipt) if receipt == accepted.receipt => {}
                Ok(_) => {
                    return VerifyReport::broken(
                        index,
                        "collective operation replay produced a different receipt",
                    );
                }
                Err(error) => {
                    return VerifyReport::broken(
                        index,
                        format!("collective operation replay refused: {error}"),
                    );
                }
            }
        }
        if replay.collective.checkpoint_wire_bytes() != session.collective.checkpoint_wire_bytes() {
            return VerifyReport::broken(
                session.accepted.len(),
                "replayed collective checkpoint differs from live encrypted state",
            );
        }
        if replay.pending_actor != session.pending_actor {
            return VerifyReport::broken(
                session.accepted.len(),
                "replayed collective pending actor differs from live surface ownership",
            );
        }
        let mut report = VerifyReport::ok(session.accepted.len());
        report.detail = format!(
            "{} collective Dark Pool transition(s) replayed; {} committed swap(s), {} pending candidate; the host retains public BFV material only",
            session.accepted.len(),
            session.collective.next_sequence(),
            usize::from(session.collective.has_pending_candidate()),
        );
        report
    }

    fn render(&self, session: &Self::Session) -> Surface {
        let public = session
            .collective
            .public_session()
            .expect("a constructed collective session retains a valid public view");
        let status = if session.collective.has_pending_candidate() {
            "Candidate staged · awaiting an independent FHDAR authority decision"
        } else {
            "Open for one collective-key encrypted candidate"
        };
        Surface(ViewNode::Section {
            title: "The Dark Bazaar — collective encrypted table".to_string(),
            tag: "accent".to_string(),
            children: vec![
                ViewNode::Section {
                    title: "Public game state".to_string(),
                    tag: "genuine".to_string(),
                    children: vec![
                        ViewNode::Text(status.to_string()),
                        ViewNode::Text(format!(
                            "{} committed swap(s) · invariant k={} · next sequence {}",
                            session.collective.next_sequence(),
                            public.k(),
                            public.next_sequence(),
                        )),
                        ViewNode::Text(format!(
                            "{} custodians · Tier-1 threshold {} · decision threshold {}",
                            session.collective.config.keygen.n_parties(),
                            session
                                .collective
                                .config
                                .same_opening_verifier
                                .threshold(),
                            session
                                .collective
                                .config
                                .decision_policy
                                .verifier()
                                .threshold(),
                        )),
                        ViewNode::Text(format!(
                            "current semantic root {} · public carrier {}",
                            short_root(&session.collective.current_root()),
                            short_digest(
                                &session.collective.public_host_material().material_digest()
                            ),
                        )),
                        ViewNode::Text(match &session.pending_actor {
                            Some(actor) => format!(
                                "pending candidate belongs to frontend actor {}",
                                short_identity(actor.as_str())
                            ),
                            None => "no frontend actor currently owns the staging slot".to_string(),
                        }),
                        ViewNode::Text(
                            "Reserves, swap amounts, BFV secret keys, decryption shares, MPC operands, and same-opening witnesses are absent from this host surface."
                                .to_string(),
                        ),
                    ],
                },
                ViewNode::Section {
                    title: "Two-authority lifecycle".to_string(),
                    tag: "muted".to_string(),
                    children: vec![ViewNode::Text(if session.collective.has_pending_candidate() {
                        DARK_AMM_COLLECTIVE_COMMIT_DISCLOSURE.to_string()
                    } else {
                        DARK_AMM_COLLECTIVE_STAGE_DISCLOSURE.to_string()
                    })],
                },
            ],
        })
    }

    fn binary_artifacts(&self, session: &Self::Session) -> Vec<BinaryArtifactDescriptor> {
        if !session.collective.has_pending_candidate() {
            return Vec::new();
        }
        vec![BinaryArtifactDescriptor {
            name: DARK_AMM_COLLECTIVE_TASK_ARTIFACT.to_string(),
            title: "Download the collective authority work item".to_string(),
            media_type: DARK_AMM_COLLECTIVE_TASK_MEDIA_TYPE.to_string(),
            max_bytes: MAX_COLLECTIVE_DECISION_TASK_BYTES,
            disclosure: DARK_AMM_COLLECTIVE_TASK_DISCLOSURE.to_string(),
            visibility: BinaryArtifactVisibility::Public,
        }]
    }

    fn export_binary_artifact(
        &self,
        session: &Self::Session,
        name: &str,
    ) -> Result<Vec<u8>, BinaryArtifactError> {
        if name != DARK_AMM_COLLECTIVE_TASK_ARTIFACT {
            return Err(BinaryArtifactError::UnknownArtifact(name.to_string()));
        }
        session
            .pending_decision_task()
            .and_then(|task| {
                task.to_wire_bytes().map_err(|error| {
                    CollectiveDarkAmmError::Refused(format!("decision task refused: {error}"))
                })
            })
            .map_err(|error| BinaryArtifactError::Refused(error.to_string()))
    }

    fn binary_operations(&self, session: &Self::Session) -> Vec<BinaryOperationDescriptor> {
        if session.collective.has_pending_candidate() {
            vec![
                BinaryOperationDescriptor {
                    name: DARK_AMM_COLLECTIVE_COMMIT_OPERATION.to_string(),
                    title: "Commit the authority-approved encrypted candidate".to_string(),
                    input_media_type: DARK_AMM_COLLECTIVE_COMMIT_MEDIA_TYPE.to_string(),
                    max_input_bytes: MAX_COLLECTIVE_DECISION_BUNDLE_BYTES,
                    disclosure: DARK_AMM_COLLECTIVE_COMMIT_DISCLOSURE.to_string(),
                },
                BinaryOperationDescriptor {
                    name: DARK_AMM_COLLECTIVE_ABANDON_OPERATION.to_string(),
                    title: "Abandon this staged candidate".to_string(),
                    input_media_type: DARK_AMM_COLLECTIVE_ABANDON_MEDIA_TYPE.to_string(),
                    max_input_bytes: DARK_AMM_COLLECTIVE_ABANDON_BYTES,
                    disclosure: DARK_AMM_COLLECTIVE_ABANDON_DISCLOSURE.to_string(),
                },
            ]
        } else {
            vec![BinaryOperationDescriptor {
                name: DARK_AMM_COLLECTIVE_STAGE_OPERATION.to_string(),
                title: "Stage a proof-bound collective-key Dark Pool candidate".to_string(),
                input_media_type: DARK_AMM_COLLECTIVE_STAGE_MEDIA_TYPE.to_string(),
                max_input_bytes: MAX_DARK_AMM_REQUEST_BYTES,
                disclosure: DARK_AMM_COLLECTIVE_STAGE_DISCLOSURE.to_string(),
            }]
        }
    }

    fn binary_operation_replay_material(
        &self,
        session: &Self::Session,
        name: &str,
        payload: &[u8],
    ) -> Result<Option<BinaryOperationReplayMaterial>, BinaryOperationError> {
        match name {
            DARK_AMM_COLLECTIVE_STAGE_OPERATION if !session.collective.has_pending_candidate() => {
                let request = SameOpeningProvedEncryptedSwapRequest::from_wire_bytes(payload)
                    .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
                let canonical = request.to_wire_bytes();
                if canonical != payload {
                    return Err(BinaryOperationError::Malformed(
                        "collective stage request is not canonical".to_string(),
                    ));
                }
                Ok(Some(BinaryOperationReplayMaterial::new(
                    canonical,
                    DARK_AMM_COLLECTIVE_STAGE_DISCLOSURE,
                )))
            }
            DARK_AMM_COLLECTIVE_COMMIT_OPERATION if session.collective.has_pending_candidate() => {
                let bundle = CollectiveDecisionBundle::from_wire_bytes(payload)
                    .map_err(map_collective_operation_error)?;
                Ok(Some(BinaryOperationReplayMaterial::new(
                    bundle
                        .to_wire_bytes()
                        .map_err(map_collective_operation_error)?,
                    DARK_AMM_COLLECTIVE_COMMIT_DISCLOSURE,
                )))
            }
            DARK_AMM_COLLECTIVE_ABANDON_OPERATION if session.collective.has_pending_candidate() => {
                let digest = decode_abandon_digest(payload)?;
                let expected = session
                    .collective
                    .pending_decision_task()
                    .and_then(|task| {
                        task.attestation_nonce().map_err(|error| {
                            CollectiveDarkAmmError::Refused(format!(
                                "decision task refused: {error}"
                            ))
                        })
                    })
                    .map_err(map_collective_operation_error)?;
                if digest != expected {
                    return Err(BinaryOperationError::Refused(
                        "abandon request names a different pending decision task".to_string(),
                    ));
                }
                Ok(Some(BinaryOperationReplayMaterial::new(
                    payload.to_vec(),
                    DARK_AMM_COLLECTIVE_ABANDON_DISCLOSURE,
                )))
            }
            _ => Err(BinaryOperationError::UnknownOperation(name.to_string())),
        }
    }

    fn invoke_binary_operation(
        &self,
        session: &mut Self::Session,
        name: &str,
        payload: &[u8],
        actor: DreggIdentity,
    ) -> Result<BinaryOperationReceipt, BinaryOperationError> {
        let (operation, canonical_payload, receipt) = match name {
            DARK_AMM_COLLECTIVE_STAGE_OPERATION if !session.collective.has_pending_candidate() => {
                let receipt = self.execute_stage(session, payload, &actor)?;
                (
                    DARK_AMM_COLLECTIVE_STAGE_OPERATION,
                    payload.to_vec(),
                    receipt,
                )
            }
            DARK_AMM_COLLECTIVE_COMMIT_OPERATION if session.collective.has_pending_candidate() => {
                let receipt = self.execute_commit(session, payload, &actor)?;
                (
                    DARK_AMM_COLLECTIVE_COMMIT_OPERATION,
                    payload.to_vec(),
                    receipt,
                )
            }
            DARK_AMM_COLLECTIVE_ABANDON_OPERATION if session.collective.has_pending_candidate() => {
                let receipt = self.execute_abandon(session, payload, &actor)?;
                (
                    DARK_AMM_COLLECTIVE_ABANDON_OPERATION,
                    payload.to_vec(),
                    receipt,
                )
            }
            _ => return Err(BinaryOperationError::UnknownOperation(name.to_string())),
        };
        session.accepted.push(AcceptedCollectiveOperation {
            operation,
            canonical_payload,
            actor,
            receipt: receipt.clone(),
        });
        Ok(receipt)
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

fn decode_request(
    bytes: &[u8],
) -> Result<SameOpeningProvedEncryptedSwapRequest, CollectiveDarkAmmError> {
    let request = SameOpeningProvedEncryptedSwapRequest::from_wire_bytes(bytes)
        .map_err(|error| CollectiveDarkAmmError::Malformed(error.to_string()))?;
    if request.to_wire_bytes() != bytes {
        return Err(CollectiveDarkAmmError::Malformed(
            "strict-v3 request is not canonical".to_string(),
        ));
    }
    Ok(request)
}

fn validate_root(root: [u32; 8]) -> Result<(), CollectiveDarkAmmError> {
    if root.iter().any(|lane| *lane >= BABYBEAR_P) {
        return Err(CollectiveDarkAmmError::Configuration(
            "HidingFri root contains a noncanonical BabyBear element".to_string(),
        ));
    }
    Ok(())
}

fn replay_context(
    lane: &[u8],
    hosted_session: &[u8; 32],
    verifier_id: &[u8; 32],
    collective_identity_digest: &[u8; 32],
) -> [u8; 32] {
    let mut hash = blake3::Hasher::new_derive_key(REPLAY_CONTEXT_DOMAIN);
    hash.update(&(lane.len() as u64).to_le_bytes());
    hash.update(lane);
    hash.update(hosted_session);
    hash.update(verifier_id);
    hash.update(collective_identity_digest);
    *hash.finalize().as_bytes()
}

fn collective_identity_digest(
    params: &BfvParams,
    keygen: &KeygenSession,
    collective: &CollectivePublicKey,
) -> [u8; 32] {
    let mut hash =
        blake3::Hasher::new_derive_key("dregg-dark-amm-collective-bfv-public-identity-v2");
    hash.update(&canonical_bfv_parameters_digest(params.arc()));
    hash.update(&(keygen.n_parties() as u64).to_le_bytes());
    hash.update(&keygen.crp_seed());
    let public_key = collective.pk.to_bytes();
    hash.update(&(public_key.len() as u64).to_le_bytes());
    hash.update(&public_key);
    *hash.finalize().as_bytes()
}

fn checkpoint_checksum(content: &[u8]) -> [u8; 32] {
    let mut hash = blake3::Hasher::new_derive_key(CHECKPOINT_DOMAIN);
    hash.update(&(content.len() as u64).to_le_bytes());
    hash.update(content);
    *hash.finalize().as_bytes()
}

fn put_u64(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_bytes(out: &mut Vec<u8>, bytes: &[u8]) {
    put_u64(out, bytes.len() as u64);
    out.extend_from_slice(bytes);
}

fn map_collective_operation_error(error: CollectiveDarkAmmError) -> BinaryOperationError {
    match error {
        CollectiveDarkAmmError::Malformed(reason) => BinaryOperationError::Malformed(reason),
        other => BinaryOperationError::Refused(other.to_string()),
    }
}

fn decode_abandon_digest(payload: &[u8]) -> Result<[u8; 32], BinaryOperationError> {
    payload.try_into().map_err(|_| {
        BinaryOperationError::Malformed(format!(
            "collective abandon body must be exactly {DARK_AMM_COLLECTIVE_ABANDON_BYTES} bytes"
        ))
    })
}

fn require_pending_actor(
    session: &CollectiveDarkAmmGameSession,
    actor: &DreggIdentity,
) -> Result<(), BinaryOperationError> {
    match &session.pending_actor {
        Some(owner) if owner == actor => Ok(()),
        Some(_) => Err(BinaryOperationError::Refused(
            "only the frontend actor that staged this candidate may finish or abandon it"
                .to_string(),
        )),
        None => Err(BinaryOperationError::Refused(
            "pending collective candidate has no frontend owner".to_string(),
        )),
    }
}

fn bind_actor(
    hash: &mut blake3::Hasher,
    actor: &DreggIdentity,
) -> Result<(), BinaryOperationError> {
    let actor = actor.as_str().as_bytes();
    let len = u64::try_from(actor.len())
        .map_err(|_| BinaryOperationError::Refused("actor identity is too long".to_string()))?;
    hash.update(&len.to_le_bytes());
    hash.update(actor);
    Ok(())
}

fn short_identity(identity: &str) -> String {
    const DISPLAY_CHARS: usize = 18;
    if identity.chars().count() <= DISPLAY_CHARS {
        return identity.to_string();
    }
    format!(
        "{}…",
        identity.chars().take(DISPLAY_CHARS).collect::<String>()
    )
}

fn hex_digest(bytes: &[u8; 32]) -> String {
    let mut out = String::with_capacity(64);
    for byte in bytes {
        use std::fmt::Write as _;
        let _ = write!(out, "{byte:02x}");
    }
    out
}

fn short_digest(bytes: &[u8; 32]) -> String {
    hex_digest(bytes)[..12].to_string()
}

fn hex_root(root: &[u32; 8]) -> String {
    let mut out = String::with_capacity(64);
    for lane in root {
        use std::fmt::Write as _;
        let _ = write!(out, "{lane:08x}");
    }
    out
}

fn short_root(root: &[u32; 8]) -> String {
    hex_root(root)[..12].to_string()
}

struct DecisionBundleReader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> DecisionBundleReader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N], CollectiveDarkAmmError> {
        let end = self
            .offset
            .checked_add(N)
            .filter(|end| *end <= self.bytes.len())
            .ok_or_else(|| {
                CollectiveDarkAmmError::Malformed("truncated decision bundle".to_string())
            })?;
        let value = self.bytes[self.offset..end].try_into().map_err(|_| {
            CollectiveDarkAmmError::Malformed("invalid decision bundle field".to_string())
        })?;
        self.offset = end;
        Ok(value)
    }

    fn u64(&mut self) -> Result<u64, CollectiveDarkAmmError> {
        Ok(u64::from_le_bytes(self.array()?))
    }

    fn bytes(&mut self, max: usize) -> Result<&'a [u8], CollectiveDarkAmmError> {
        let len = usize::try_from(self.u64()?).map_err(|_| {
            CollectiveDarkAmmError::Malformed("decision bundle length overflow".to_string())
        })?;
        if len > max {
            return Err(CollectiveDarkAmmError::Malformed(format!(
                "decision bundle member length {len} exceeds maximum {max}"
            )));
        }
        let end = self
            .offset
            .checked_add(len)
            .filter(|end| *end <= self.bytes.len())
            .ok_or_else(|| {
                CollectiveDarkAmmError::Malformed("truncated decision bundle".to_string())
            })?;
        let value = &self.bytes[self.offset..end];
        self.offset = end;
        Ok(value)
    }

    fn finish(self) -> Result<(), CollectiveDarkAmmError> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err(CollectiveDarkAmmError::Malformed(
                "trailing decision bundle bytes".to_string(),
            ))
        }
    }
}

struct PendingRef<'a> {
    request_wire: &'a [u8],
    same_opening_claim_digest: [u8; 32],
    candidate_nonce: [u8; 32],
}

struct DecodedCheckpoint<'a> {
    hosted_session: [u8; 32],
    current_root: [u32; 8],
    next_sequence: u64,
    material_wire: &'a [u8],
    same_opening_replay_wire: &'a [u8],
    decision_replay_wire: &'a [u8],
    pending: Option<PendingRef<'a>>,
}

impl<'a> DecodedCheckpoint<'a> {
    fn parse(bytes: &'a [u8]) -> Result<Self, CollectiveDarkAmmError> {
        if bytes.len() > MAX_CHECKPOINT_BYTES || bytes.len() < 8 + 32 + 32 + 8 + 3 * 8 + 1 + 32 {
            return Err(CollectiveDarkAmmError::Malformed(
                "checkpoint size is outside fixed bounds".to_string(),
            ));
        }
        let content_end = bytes.len() - 32;
        if bytes[content_end..] != checkpoint_checksum(&bytes[..content_end]) {
            return Err(CollectiveDarkAmmError::Malformed(
                "checkpoint checksum mismatch".to_string(),
            ));
        }
        let mut reader = CheckpointReader::new(&bytes[..content_end]);
        if reader.array::<8>()? != *CHECKPOINT_MAGIC {
            return Err(CollectiveDarkAmmError::Malformed(
                "wrong checkpoint version".to_string(),
            ));
        }
        let hosted_session = reader.array()?;
        let mut current_root = [0u32; 8];
        for lane in &mut current_root {
            *lane = u32::from_le_bytes(reader.array()?);
        }
        let next_sequence = reader.u64()?;
        let material_wire = reader.bytes(MAX_DARK_AMM_PUBLIC_HOST_MATERIAL_BYTES)?;
        let same_opening_replay_wire = reader.bytes(MAX_REPLAY_WIRE_BYTES)?;
        let decision_replay_wire = reader.bytes(MAX_REPLAY_WIRE_BYTES)?;
        let pending = match reader.byte()? {
            0 => None,
            1 => Some(PendingRef {
                request_wire: reader.bytes(MAX_DARK_AMM_REQUEST_BYTES)?,
                same_opening_claim_digest: reader.array()?,
                candidate_nonce: reader.array()?,
            }),
            other => {
                return Err(CollectiveDarkAmmError::Malformed(format!(
                    "unknown pending tag {other}"
                )));
            }
        };
        reader.finish()?;
        Ok(Self {
            hosted_session,
            current_root,
            next_sequence,
            material_wire,
            same_opening_replay_wire,
            decision_replay_wire,
            pending,
        })
    }
}

struct CheckpointReader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> CheckpointReader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N], CollectiveDarkAmmError> {
        let end = self
            .offset
            .checked_add(N)
            .filter(|end| *end <= self.bytes.len())
            .ok_or_else(|| CollectiveDarkAmmError::Malformed("truncated checkpoint".to_string()))?;
        let value = self.bytes[self.offset..end]
            .try_into()
            .map_err(|_| CollectiveDarkAmmError::Malformed("invalid fixed field".to_string()))?;
        self.offset = end;
        Ok(value)
    }

    fn byte(&mut self) -> Result<u8, CollectiveDarkAmmError> {
        Ok(self.array::<1>()?[0])
    }

    fn u64(&mut self) -> Result<u64, CollectiveDarkAmmError> {
        Ok(u64::from_le_bytes(self.array()?))
    }

    fn bytes(&mut self, max: usize) -> Result<&'a [u8], CollectiveDarkAmmError> {
        let len = usize::try_from(self.u64()?).map_err(|_| {
            CollectiveDarkAmmError::Malformed("checkpoint length overflow".to_string())
        })?;
        if len > max {
            return Err(CollectiveDarkAmmError::Malformed(format!(
                "checkpoint field length {len} exceeds maximum {max}"
            )));
        }
        let end = self
            .offset
            .checked_add(len)
            .filter(|end| *end <= self.bytes.len())
            .ok_or_else(|| CollectiveDarkAmmError::Malformed("truncated checkpoint".to_string()))?;
        let value = &self.bytes[self.offset..end];
        self.offset = end;
        Ok(value)
    }

    fn finish(self) -> Result<(), CollectiveDarkAmmError> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err(CollectiveDarkAmmError::Malformed(
                "trailing checkpoint bytes".to_string(),
            ))
        }
    }
}
