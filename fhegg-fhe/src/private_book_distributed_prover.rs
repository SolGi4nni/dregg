//! Process boundary between secret-shared private-book inputs and a future
//! malicious-secure distributed R1CS prover.
//!
//! [`WorkerProofProcess`] is the only type in this module that accepts a
//! [`PreparedWitnessShare`].  It authenticates the worker identity, verifies
//! one canonical [`ShareBoundProverRequest`], verifies the complete public
//! input certificate, checks that the private capability names the
//! certificate's exact four owner dealings, and then moves that capability
//! into a worker-local backend.  The request has a fixed-size public wire: its
//! only admitted custody mode is distributed shares, and appended plaintext
//! witness/opening bytes are not representable.  The public
//! [`DistributedProverCoordinator`] has no method or field that accepts a
//! private share; it collects only bounded public proof artifacts plus their
//! roster-signed transcript digests.  A proof artifact is an explicitly public
//! backend output, never a witness-data plane.
//! Deployments put one `WorkerProofProcess` and its backend in each proof
//! worker's isolated process and give the coordinator only
//! [`WorkerProofContribution`] values.
//!
//! # Exact cryptographic guarantee
//!
//! The resulting [`DistributedProverEnvelope`] binds every worker's bounded
//! public backend proof under the same
//! session, relation digest, input-certificate transcript, joint hiding input
//! commitment, worker count, and backend protocol identifier.  Ed25519
//! authenticates participation and BLAKE3 binds the transcript.  Moving the
//! non-`Clone` share into a worker-local backend prevents this coordinator API
//! from materializing the full witness.
//!
//! This envelope is **not by itself** an R1CS proof, is not evidence that a
//! backend ran correct MPC, and does not make a malicious backend zero
//! knowledge. A concrete backend must implement [`WorkerLocalProofBackend`]
//! and its direct public verifier must implement
//! [`PublicDistributedProofVerifier`]. The canonical share-opening backend
//! proves committed-share custody plus its named linear constraints. The input
//! certificate separately proves owner-local kind/quantity ranges linked to
//! those same distributed commitments, but not yet the full nonlinear
//! BFV/Poseidon/selector-table/clearing relation. The monolithic
//! `private_book_bfv_zk::prove_private_book_bfv_zk` therefore remains the
//! explicit Tier-1 full-relation path: its one prover process sees all four
//! orders and BFV seeds. Public artifact bytes are size-bounded, but a
//! malicious backend can still use any public output as a covert channel for
//! low-entropy secrets; the final no-leak claim belongs to the concrete
//! distributed backend and proof wire.

use std::fmt;
use std::iter;

use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};

use crate::private_book_distributed_inputs::{
    DistributedInputCertificate, DistributedInputError, DistributedWitnessSession,
    PreparedWitnessShare,
};

const CONTEXT_DOMAIN: &str = "fhegg/private-book-distributed-prover/context/v1";
const REQUEST_CHECKSUM_DOMAIN: &str = "fhegg/private-book-distributed-prover/request-checksum/v1";
const CONTRIBUTION_DOMAIN: &str = "fhegg/private-book-distributed-prover/contribution/v1";
const BUNDLE_DOMAIN: &str = "fhegg/private-book-distributed-prover/bundle/v1";
const BACKEND_ARTIFACT_DOMAIN: &str = "fhegg/private-book-distributed-prover/backend-artifact/v1";
const WIRE_CHECKSUM_DOMAIN: &str = "fhegg/private-book-distributed-prover/wire-checksum/v1";
const SIGNATURE_DOMAIN: &[u8] = b"fhegg/private-book-distributed-prover/signature/v1";
const REQUEST_MAGIC: &[u8; 8] = b"FHPRQ001";
const REQUEST_VERSION: u16 = 1;
const DISTRIBUTED_SHARES_MODE: u8 = 1;
const REQUEST_WIRE_LEN: usize = 8 + 2 + 1 + 1 + 5 * 32 + 2 + 32 + 32;
const CONTRIBUTION_MAGIC: &[u8; 8] = b"FHPWC002";
const CONTRIBUTION_VERSION: u16 = 2;
const CONTRIBUTION_FIXED_WIRE_LEN: usize = 8 + 2 + 2 + 4 + 6 * 32 + 64 + 32;
/// Exhaustion ceiling for one worker's public backend proof.  The current
/// logarithmic share-opening proof is below 8 KiB at degree 4096.
pub const MAX_PUBLIC_BACKEND_ARTIFACT_BYTES: usize = 2 * 1024 * 1024;

/// Fail-closed errors at the distributed-prover custody boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DistributedProverError {
    Input(DistributedInputError),
    WorkerOutOfRange,
    SigningKeyMismatch,
    InvalidProtocol,
    MalformedRequest,
    SourceViewerForbidden,
    RequestMismatch,
    WitnessMisbound,
    InputCertificateMismatch,
    ProtocolMismatch,
    InvalidBackendTranscript,
    InvalidBackendArtifact,
    ContributionDigestMismatch,
    InvalidSignature,
    MalformedContribution,
    DuplicateContribution,
    MissingContributions,
    BundleDigestMismatch,
    BackendRejected,
}

impl fmt::Display for DistributedProverError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Input(error) => write!(f, "distributed input rejected: {error}"),
            Self::WorkerOutOfRange => write!(f, "distributed prover worker is out of range"),
            Self::SigningKeyMismatch => {
                write!(f, "worker signing key does not match the ceremony roster")
            }
            Self::InvalidProtocol => write!(f, "distributed prover protocol id is invalid"),
            Self::MalformedRequest => write!(f, "share-bound prover request wire is malformed"),
            Self::SourceViewerForbidden => write!(
                f,
                "monolithic plaintext/source-viewer custody is forbidden on this prover boundary"
            ),
            Self::RequestMismatch => {
                write!(f, "share-bound prover request names another public context")
            }
            Self::WitnessMisbound => {
                write!(
                    f,
                    "prepared witness share belongs to another worker or session"
                )
            }
            Self::InputCertificateMismatch => {
                write!(f, "prover contribution names another input certificate")
            }
            Self::ProtocolMismatch => {
                write!(f, "prover contribution names another backend protocol")
            }
            Self::InvalidBackendTranscript => {
                write!(f, "backend returned an invalid public transcript digest")
            }
            Self::InvalidBackendArtifact => {
                write!(f, "backend returned a malformed public proof artifact")
            }
            Self::ContributionDigestMismatch => {
                write!(f, "worker contribution transcript does not match")
            }
            Self::InvalidSignature => write!(f, "worker proof contribution signature is invalid"),
            Self::MalformedContribution => {
                write!(f, "worker proof contribution wire is malformed")
            }
            Self::DuplicateContribution => {
                write!(f, "worker proof contribution was already accepted")
            }
            Self::MissingContributions => {
                write!(f, "not every proof worker supplied a contribution")
            }
            Self::BundleDigestMismatch => {
                write!(f, "distributed prover bundle transcript does not match")
            }
            Self::BackendRejected => write!(f, "distributed proof backend rejected the protocol"),
        }
    }
}

impl std::error::Error for DistributedProverError {}

impl From<DistributedInputError> for DistributedProverError {
    fn from(error: DistributedInputError) -> Self {
        Self::Input(error)
    }
}

type Result<T> = std::result::Result<T, DistributedProverError>;

/// Bounded public output of one worker-local proof backend.
///
/// The type deliberately owns bytes: a coordinator may transport and verify a
/// zero-knowledge proof, but cannot use this API to request a private share or
/// commitment opening.  Backends remain responsible for proving that their
/// chosen public artifact is non-leaking; the generic boundary only enforces a
/// strict size and non-empty encoding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WorkerProofArtifact {
    bytes: Vec<u8>,
}

impl WorkerProofArtifact {
    pub fn new(bytes: Vec<u8>) -> Result<Self> {
        if bytes.is_empty() || bytes.len() > MAX_PUBLIC_BACKEND_ARTIFACT_BYTES {
            return Err(DistributedProverError::InvalidBackendArtifact);
        }
        Ok(Self { bytes })
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    fn transcript_digest(&self, context: &WorkerProofContext, worker: usize) -> [u8; 32] {
        hash_parts(
            BACKEND_ARTIFACT_DOMAIN,
            &[&context.digest, &(worker as u64).to_be_bytes(), &self.bytes],
        )
    }
}

/// Public, exact context supplied identically to every worker-local backend.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WorkerProofContext {
    session_digest: [u8; 32],
    relation_digest: [u8; 32],
    input_certificate_digest: [u8; 32],
    joint_input_commitment: [u8; 32],
    protocol_id: [u8; 32],
    n_workers: usize,
    digest: [u8; 32],
}

impl WorkerProofContext {
    fn new(
        session: &DistributedWitnessSession,
        certificate: &DistributedInputCertificate,
        protocol_id: [u8; 32],
    ) -> Result<Self> {
        if protocol_id == [0; 32] {
            return Err(DistributedProverError::InvalidProtocol);
        }
        let input_certificate_digest = certificate.transcript_digest();
        let joint_input_commitment = certificate.joint_input_commitment()?;
        let mut context = Self {
            session_digest: session.digest(),
            relation_digest: session.relation_digest(),
            input_certificate_digest,
            joint_input_commitment,
            protocol_id,
            n_workers: session.n_workers(),
            digest: [0; 32],
        };
        context.digest = context.compute_digest();
        Ok(context)
    }

    /// Complete ceremony/session identifier.
    pub const fn session_digest(&self) -> [u8; 32] {
        self.session_digest
    }

    /// Exact public private-book/BFV relation identifier.
    pub const fn relation_digest(&self) -> [u8; 32] {
        self.relation_digest
    }

    /// Public distributed-input certificate transcript.
    pub const fn input_certificate_digest(&self) -> [u8; 32] {
        self.input_certificate_digest
    }

    /// Hiding commitment to all four owner input vectors.
    pub const fn joint_input_commitment(&self) -> [u8; 32] {
        self.joint_input_commitment
    }

    /// Backend protocol/version identifier.
    pub const fn protocol_id(&self) -> [u8; 32] {
        self.protocol_id
    }

    /// Exact proof-worker roster size.
    pub const fn n_workers(&self) -> usize {
        self.n_workers
    }

    /// Digest signed indirectly by every worker contribution.
    pub const fn digest(&self) -> [u8; 32] {
        self.digest
    }

    fn compute_digest(&self) -> [u8; 32] {
        hash_parts(
            CONTEXT_DOMAIN,
            &[
                &self.session_digest,
                &self.relation_digest,
                &self.input_certificate_digest,
                &self.joint_input_commitment,
                &self.protocol_id,
                &(self.n_workers as u64).to_be_bytes(),
            ],
        )
    }
}

/// Canonical fixed-size request for the distributed-share prover boundary.
///
/// The request is public.  It binds the exact input certificate, joint hiding
/// commitment, relation, session, worker count, and backend protocol before a
/// private share enters a worker process.  Its wire admits exactly one custody
/// mode: `distributed-shares`.  A complete plaintext witness, BFV seed/opening,
/// or reconstructed scalar vector cannot be encoded because the parser
/// requires the exact fixed length and rejects every other custody-mode byte.
///
/// This is an API/process-boundary guarantee, not a proof that a malicious
/// distributed backend will not collude or reconstruct shares over its own
/// private channels.  That guarantee belongs to the concrete backend protocol.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShareBoundProverRequest {
    context: WorkerProofContext,
}

impl ShareBoundProverRequest {
    /// Construct a request from the exact verified distributed-input
    /// certificate.  There is deliberately no constructor taking plaintext
    /// orders, BFV seeds/openings, or a monolithic witness.
    pub fn new(
        session: &DistributedWitnessSession,
        input_certificate: &DistributedInputCertificate,
        protocol_id: [u8; 32],
    ) -> Result<Self> {
        input_certificate.verify(session)?;
        Ok(Self {
            context: WorkerProofContext::new(session, input_certificate, protocol_id)?,
        })
    }

    /// Complete request/context digest signed indirectly by every worker.
    pub const fn digest(&self) -> [u8; 32] {
        self.context.digest()
    }

    /// Exact backend protocol/version selected by this request.
    pub const fn protocol_id(&self) -> [u8; 32] {
        self.context.protocol_id()
    }

    /// Emit the sole canonical public request wire.  The one-byte custody mode
    /// is pinned to distributed shares; the following reserved byte is zero.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(REQUEST_WIRE_LEN);
        out.extend_from_slice(REQUEST_MAGIC);
        out.extend_from_slice(&REQUEST_VERSION.to_be_bytes());
        out.push(DISTRIBUTED_SHARES_MODE);
        out.push(0);
        out.extend_from_slice(&self.context.session_digest);
        out.extend_from_slice(&self.context.relation_digest);
        out.extend_from_slice(&self.context.input_certificate_digest);
        out.extend_from_slice(&self.context.joint_input_commitment);
        out.extend_from_slice(&self.context.protocol_id);
        out.extend_from_slice(&(self.context.n_workers as u16).to_be_bytes());
        out.extend_from_slice(&self.context.digest);
        let checksum = hash_parts(REQUEST_CHECKSUM_DOMAIN, &[&out]);
        out.extend_from_slice(&checksum);
        debug_assert_eq!(out.len(), REQUEST_WIRE_LEN);
        out
    }

    /// Parse an untrusted request only against independently supplied session,
    /// certificate, and backend policy.  Exact re-encoding prevents appended
    /// plaintext/source-opening data and non-canonical integer encodings.
    pub fn from_bytes(
        bytes: &[u8],
        session: &DistributedWitnessSession,
        input_certificate: &DistributedInputCertificate,
        expected_protocol_id: [u8; 32],
    ) -> Result<Self> {
        if bytes.len() != REQUEST_WIRE_LEN {
            return Err(DistributedProverError::MalformedRequest);
        }
        let mut offset = 0;
        if take_request::<8>(bytes, &mut offset)? != *REQUEST_MAGIC
            || u16::from_be_bytes(take_request::<2>(bytes, &mut offset)?) != REQUEST_VERSION
        {
            return Err(DistributedProverError::MalformedRequest);
        }
        let custody_mode = take_request::<1>(bytes, &mut offset)?[0];
        if custody_mode != DISTRIBUTED_SHARES_MODE {
            return Err(DistributedProverError::SourceViewerForbidden);
        }
        if take_request::<1>(bytes, &mut offset)? != [0] {
            return Err(DistributedProverError::MalformedRequest);
        }
        let context = WorkerProofContext {
            session_digest: take_request::<32>(bytes, &mut offset)?,
            relation_digest: take_request::<32>(bytes, &mut offset)?,
            input_certificate_digest: take_request::<32>(bytes, &mut offset)?,
            joint_input_commitment: take_request::<32>(bytes, &mut offset)?,
            protocol_id: take_request::<32>(bytes, &mut offset)?,
            n_workers: u16::from_be_bytes(take_request::<2>(bytes, &mut offset)?) as usize,
            digest: take_request::<32>(bytes, &mut offset)?,
        };
        let checksum_start = bytes.len() - 32;
        if offset != checksum_start
            || take_request::<32>(bytes, &mut offset)?
                != hash_parts(REQUEST_CHECKSUM_DOMAIN, &[&bytes[..checksum_start]])
            || offset != bytes.len()
        {
            return Err(DistributedProverError::MalformedRequest);
        }

        let expected = Self::new(session, input_certificate, expected_protocol_id)?;
        let request = Self { context };
        if request != expected || request.to_bytes() != bytes {
            return Err(DistributedProverError::RequestMismatch);
        }
        Ok(request)
    }

    fn verify(
        &self,
        session: &DistributedWitnessSession,
        input_certificate: &DistributedInputCertificate,
        expected_protocol_id: [u8; 32],
    ) -> Result<()> {
        let expected = Self::new(session, input_certificate, expected_protocol_id)?;
        if *self != expected {
            return Err(DistributedProverError::RequestMismatch);
        }
        Ok(())
    }
}

/// Secret worker-side proving implementation.
///
/// The backend may run an interactive MPC protocol over worker-only channels,
/// but it receives exactly one worker's additive capability.  Its public
/// result is one bounded canonical public proof artifact; raw scalar shares and
/// commitment blindings never enter the coordinator API.
pub trait WorkerLocalProofBackend {
    type Error;

    /// Stable identifier for the exact backend protocol and circuit version.
    fn protocol_id(&self) -> [u8; 32];

    /// Consume one worker's complete prepared share in the worker process.
    fn prove_local(
        &mut self,
        context: &WorkerProofContext,
        input_certificate: &DistributedInputCertificate,
        witness: PreparedWitnessShare,
    ) -> std::result::Result<WorkerProofArtifact, Self::Error>;
}

/// Public verifier for one backend's ordered worker proof artifacts.
///
/// It receives the bounded public bytes carried inside the signed envelope and
/// must verify the concrete cryptographic protocol directly against `context`.
pub trait PublicDistributedProofVerifier {
    type Error;

    /// Must exactly match the worker backend protocol identifier.
    fn protocol_id(&self) -> [u8; 32];

    /// Verify the complete ordered set against the canonical public proof.
    fn verify_public_artifacts(
        &self,
        context: &WorkerProofContext,
        artifacts: &[WorkerProofArtifact],
    ) -> std::result::Result<(), Self::Error>;
}

/// One-shot worker-process role.  It is intentionally neither `Clone` nor
/// `Debug`, and consuming `run` prevents accidental reuse of one role object.
pub struct WorkerProofProcess<B> {
    session: DistributedWitnessSession,
    worker: usize,
    signing_key: SigningKey,
    protocol_id: [u8; 32],
    backend: B,
}

impl<B: WorkerLocalProofBackend> WorkerProofProcess<B> {
    /// Bind a worker-local backend and signing capability to one roster slot.
    pub fn new(
        session: DistributedWitnessSession,
        worker: usize,
        signing_key: SigningKey,
        backend: B,
    ) -> Result<Self> {
        let expected_key = session
            .worker_key(worker)
            .ok_or(DistributedProverError::WorkerOutOfRange)?;
        if signing_key.verifying_key().to_bytes() != expected_key {
            return Err(DistributedProverError::SigningKeyMismatch);
        }
        let protocol_id = backend.protocol_id();
        if protocol_id == [0; 32] {
            return Err(DistributedProverError::InvalidProtocol);
        }
        Ok(Self {
            session,
            worker,
            signing_key,
            protocol_id,
            backend,
        })
    }

    /// Verify all custody bindings, move the share into the local backend, and
    /// release only its bounded public proof artifact and signed digest.
    pub fn run(
        mut self,
        request: &ShareBoundProverRequest,
        input_certificate: &DistributedInputCertificate,
        witness: PreparedWitnessShare,
    ) -> Result<WorkerProofContribution> {
        request.verify(&self.session, input_certificate, self.protocol_id)?;
        if witness.session_digest() != self.session.digest() || witness.worker() != self.worker {
            return Err(DistributedProverError::WitnessMisbound);
        }
        witness.verify_certificate_binding(input_certificate)?;
        let context = request.context;
        let backend_artifact = self
            .backend
            .prove_local(&context, input_certificate, witness)
            .map_err(|_| DistributedProverError::BackendRejected)?;
        if backend_artifact.bytes.is_empty()
            || backend_artifact.bytes.len() > MAX_PUBLIC_BACKEND_ARTIFACT_BYTES
        {
            return Err(DistributedProverError::InvalidBackendArtifact);
        }
        let backend_transcript_digest = backend_artifact.transcript_digest(&context, self.worker);
        if backend_transcript_digest == [0; 32] {
            return Err(DistributedProverError::InvalidBackendTranscript);
        }
        let digest = contribution_digest(&context, self.worker, &backend_transcript_digest);
        let contribution = WorkerProofContribution {
            session_digest: self.session.digest(),
            input_certificate_digest: input_certificate.transcript_digest(),
            context_digest: context.digest(),
            protocol_id: self.protocol_id,
            worker: self.worker,
            backend_artifact,
            backend_transcript_digest,
            digest,
            signature: self
                .signing_key
                .sign(&signature_message(&digest))
                .to_bytes(),
        };
        contribution.verify(&self.session, &context)?;
        Ok(contribution)
    }
}

/// Public, bounded roster-authenticated output from one proof worker.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WorkerProofContribution {
    session_digest: [u8; 32],
    input_certificate_digest: [u8; 32],
    context_digest: [u8; 32],
    protocol_id: [u8; 32],
    worker: usize,
    backend_artifact: WorkerProofArtifact,
    backend_transcript_digest: [u8; 32],
    digest: [u8; 32],
    signature: [u8; 64],
}

impl WorkerProofContribution {
    /// Roster index that produced this transcript digest.
    pub const fn worker(&self) -> usize {
        self.worker
    }

    /// Digest of the backend's canonical public proof transcript.
    pub const fn backend_transcript_digest(&self) -> [u8; 32] {
        self.backend_transcript_digest
    }

    /// Signed digest of the complete worker contribution.
    pub const fn digest(&self) -> [u8; 32] {
        self.digest
    }

    /// Strict bounded public wire emitted by a separate worker process.
    /// Private scalar shares are not representable here; the length-delimited
    /// backend artifact is explicitly public proof material.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out =
            Vec::with_capacity(CONTRIBUTION_FIXED_WIRE_LEN + self.backend_artifact.bytes.len());
        out.extend_from_slice(CONTRIBUTION_MAGIC);
        out.extend_from_slice(&CONTRIBUTION_VERSION.to_be_bytes());
        out.extend_from_slice(&(self.worker as u16).to_be_bytes());
        out.extend_from_slice(&(self.backend_artifact.bytes.len() as u32).to_be_bytes());
        out.extend_from_slice(&self.session_digest);
        out.extend_from_slice(&self.input_certificate_digest);
        out.extend_from_slice(&self.context_digest);
        out.extend_from_slice(&self.protocol_id);
        out.extend_from_slice(&self.backend_transcript_digest);
        out.extend_from_slice(&self.backend_artifact.bytes);
        out.extend_from_slice(&self.digest);
        out.extend_from_slice(&self.signature);
        let checksum = hash_parts(WIRE_CHECKSUM_DOMAIN, &[&out]);
        out.extend_from_slice(&checksum);
        debug_assert_eq!(
            out.len(),
            CONTRIBUTION_FIXED_WIRE_LEN + self.backend_artifact.bytes.len()
        );
        out
    }

    /// Parse and authenticate one worker-process output against exact public
    /// session, certificate, and backend policy.
    pub fn from_bytes(
        bytes: &[u8],
        session: &DistributedWitnessSession,
        input_certificate: &DistributedInputCertificate,
        request: &ShareBoundProverRequest,
    ) -> Result<Self> {
        if bytes.len() < CONTRIBUTION_FIXED_WIRE_LEN
            || bytes.len() > CONTRIBUTION_FIXED_WIRE_LEN + MAX_PUBLIC_BACKEND_ARTIFACT_BYTES
        {
            return Err(DistributedProverError::MalformedContribution);
        }
        let checksum_start = bytes.len() - 32;
        if bytes[checksum_start..] != hash_parts(WIRE_CHECKSUM_DOMAIN, &[&bytes[..checksum_start]])
        {
            return Err(DistributedProverError::MalformedContribution);
        }
        let mut offset = 0;
        if take::<8>(bytes, &mut offset)? != *CONTRIBUTION_MAGIC
            || u16::from_be_bytes(take::<2>(bytes, &mut offset)?) != CONTRIBUTION_VERSION
        {
            return Err(DistributedProverError::MalformedContribution);
        }
        let worker = u16::from_be_bytes(take::<2>(bytes, &mut offset)?) as usize;
        let artifact_len = u32::from_be_bytes(take::<4>(bytes, &mut offset)?) as usize;
        if artifact_len == 0 || artifact_len > MAX_PUBLIC_BACKEND_ARTIFACT_BYTES {
            return Err(DistributedProverError::InvalidBackendArtifact);
        }
        let expected_len = CONTRIBUTION_FIXED_WIRE_LEN
            .checked_add(artifact_len)
            .ok_or(DistributedProverError::MalformedContribution)?;
        if bytes.len() != expected_len {
            return Err(DistributedProverError::MalformedContribution);
        }
        let session_digest = take::<32>(bytes, &mut offset)?;
        let input_certificate_digest = take::<32>(bytes, &mut offset)?;
        let context_digest = take::<32>(bytes, &mut offset)?;
        let protocol_id = take::<32>(bytes, &mut offset)?;
        let backend_transcript_digest = take::<32>(bytes, &mut offset)?;
        let artifact_end = offset
            .checked_add(artifact_len)
            .ok_or(DistributedProverError::MalformedContribution)?;
        let backend_artifact = WorkerProofArtifact::new(
            bytes
                .get(offset..artifact_end)
                .ok_or(DistributedProverError::MalformedContribution)?
                .to_vec(),
        )?;
        offset = artifact_end;
        let contribution = Self {
            session_digest,
            input_certificate_digest,
            context_digest,
            protocol_id,
            worker,
            backend_artifact,
            backend_transcript_digest,
            digest: take::<32>(bytes, &mut offset)?,
            signature: take::<64>(bytes, &mut offset)?,
        };
        if offset != checksum_start {
            return Err(DistributedProverError::MalformedContribution);
        }
        request.verify(session, input_certificate, request.protocol_id())?;
        let context = request.context;
        contribution.verify(session, &context)?;
        if contribution.to_bytes() != bytes {
            return Err(DistributedProverError::MalformedContribution);
        }
        Ok(contribution)
    }

    fn verify(
        &self,
        session: &DistributedWitnessSession,
        context: &WorkerProofContext,
    ) -> Result<()> {
        if self.worker >= session.n_workers() {
            return Err(DistributedProverError::WorkerOutOfRange);
        }
        if self.session_digest != session.digest()
            || self.input_certificate_digest != context.input_certificate_digest()
        {
            return Err(DistributedProverError::InputCertificateMismatch);
        }
        if self.protocol_id != context.protocol_id() {
            return Err(DistributedProverError::ProtocolMismatch);
        }
        if self.context_digest != context.digest() {
            return Err(DistributedProverError::ContributionDigestMismatch);
        }
        if self.backend_transcript_digest == [0; 32] {
            return Err(DistributedProverError::InvalidBackendTranscript);
        }
        if self.backend_transcript_digest
            != self
                .backend_artifact
                .transcript_digest(context, self.worker)
        {
            return Err(DistributedProverError::InvalidBackendArtifact);
        }
        let expected_digest =
            contribution_digest(context, self.worker, &self.backend_transcript_digest);
        if self.digest != expected_digest {
            return Err(DistributedProverError::ContributionDigestMismatch);
        }
        let verifying_key = VerifyingKey::from_bytes(
            &session
                .worker_key(self.worker)
                .ok_or(DistributedProverError::WorkerOutOfRange)?,
        )
        .map_err(|_| DistributedProverError::InvalidSignature)?;
        verifying_key
            .verify_strict(
                &signature_message(&self.digest),
                &Signature::from_bytes(&self.signature),
            )
            .map_err(|_| DistributedProverError::InvalidSignature)
    }

    #[cfg(test)]
    pub(crate) fn corrupt_signature_for_test(&mut self) {
        self.signature[0] ^= 1;
    }
}

/// Public-only coordinator.  Its API cannot receive `PreparedWitnessShare`.
pub struct DistributedProverCoordinator {
    session: DistributedWitnessSession,
    context: WorkerProofContext,
    contributions: Vec<Option<WorkerProofContribution>>,
}

impl DistributedProverCoordinator {
    /// Bind the public collector to one exact input certificate and backend.
    pub fn new(
        session: DistributedWitnessSession,
        request: &ShareBoundProverRequest,
        input_certificate: &DistributedInputCertificate,
    ) -> Result<Self> {
        request.verify(&session, input_certificate, request.protocol_id())?;
        let context = request.context;
        let contributions = iter::repeat_with(|| None)
            .take(session.n_workers())
            .collect();
        Ok(Self {
            session,
            context,
            contributions,
        })
    }

    /// Accept one roster-signed bounded backend proof artifact.
    pub fn accept(&mut self, contribution: WorkerProofContribution) -> Result<()> {
        contribution.verify(&self.session, &self.context)?;
        let slot = &mut self.contributions[contribution.worker];
        if slot.is_some() {
            return Err(DistributedProverError::DuplicateContribution);
        }
        *slot = Some(contribution);
        Ok(())
    }

    /// Finish only after every roster worker contributed exactly once.
    pub fn finish(self) -> Result<DistributedProverEnvelope> {
        if self.contributions.iter().any(Option::is_none) {
            return Err(DistributedProverError::MissingContributions);
        }
        let contributions = self
            .contributions
            .into_iter()
            .map(|contribution| contribution.expect("all worker contributions checked above"))
            .collect::<Vec<_>>();
        let transcript_digest = bundle_digest(&self.context, &contributions);
        Ok(DistributedProverEnvelope {
            context: self.context,
            contributions,
            transcript_digest,
        })
    }
}

/// Complete ordered public transcript from the distributed-prover boundary.
///
/// This is an authenticated carrier for backend public proofs, not itself a
/// proof that the hidden relation is satisfied.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DistributedProverEnvelope {
    context: WorkerProofContext,
    contributions: Vec<WorkerProofContribution>,
    transcript_digest: [u8; 32],
}

impl DistributedProverEnvelope {
    /// Context bound by every contribution.
    pub const fn context(&self) -> &WorkerProofContext {
        &self.context
    }

    /// Canonical public bundle transcript digest.
    pub const fn transcript_digest(&self) -> [u8; 32] {
        self.transcript_digest
    }

    /// Exact share-bound request digest authenticated by every contribution.
    pub const fn request_digest(&self) -> [u8; 32] {
        self.context.digest()
    }

    /// Ordered public transcript digests, one per worker roster slot.
    pub fn worker_transcript_digests(
        &self,
    ) -> impl ExactSizeIterator<Item = (usize, [u8; 32])> + '_ {
        self.contributions
            .iter()
            .map(|contribution| (contribution.worker, contribution.backend_transcript_digest))
    }

    /// Ordered bounded public proof artifacts, never private shares/openings.
    pub fn worker_public_artifacts(&self) -> impl ExactSizeIterator<Item = (usize, &[u8])> + '_ {
        self.contributions.iter().map(|contribution| {
            (
                contribution.worker,
                contribution.backend_artifact.as_bytes(),
            )
        })
    }

    /// Verify input binding, roster completeness, signatures, and transcript.
    /// This deliberately does not interpret the backend proof artifacts.
    pub fn verify_envelope(
        &self,
        session: &DistributedWitnessSession,
        request: &ShareBoundProverRequest,
        input_certificate: &DistributedInputCertificate,
    ) -> Result<()> {
        request.verify(session, input_certificate, self.context.protocol_id)?;
        if self.context != request.context {
            return Err(DistributedProverError::InputCertificateMismatch);
        }
        if self.contributions.len() != session.n_workers() {
            return Err(DistributedProverError::MissingContributions);
        }
        for (worker, contribution) in self.contributions.iter().enumerate() {
            if contribution.worker != worker {
                return Err(DistributedProverError::WorkerOutOfRange);
            }
            contribution.verify(session, &self.context)?;
        }
        if self.transcript_digest != bundle_digest(&self.context, &self.contributions) {
            return Err(DistributedProverError::BundleDigestMismatch);
        }
        Ok(())
    }

    /// Run the backend-specific public verifier only after the custody envelope
    /// is known to be complete and correctly bound.
    pub fn verify_backend<V: PublicDistributedProofVerifier>(
        &self,
        session: &DistributedWitnessSession,
        request: &ShareBoundProverRequest,
        input_certificate: &DistributedInputCertificate,
        verifier: &V,
    ) -> Result<()> {
        self.verify_envelope(session, request, input_certificate)?;
        if verifier.protocol_id() != self.context.protocol_id {
            return Err(DistributedProverError::ProtocolMismatch);
        }
        let artifacts = self
            .contributions
            .iter()
            .map(|contribution| contribution.backend_artifact.clone())
            .collect::<Vec<_>>();
        verifier
            .verify_public_artifacts(&self.context, &artifacts)
            .map_err(|_| DistributedProverError::BackendRejected)
    }
}

fn contribution_digest(
    context: &WorkerProofContext,
    worker: usize,
    backend_transcript_digest: &[u8; 32],
) -> [u8; 32] {
    hash_parts(
        CONTRIBUTION_DOMAIN,
        &[
            &context.digest,
            &(worker as u64).to_be_bytes(),
            backend_transcript_digest,
        ],
    )
}

fn bundle_digest(
    context: &WorkerProofContext,
    contributions: &[WorkerProofContribution],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(BUNDLE_DOMAIN);
    hasher.update(&context.digest);
    hasher.update(&(contributions.len() as u64).to_be_bytes());
    for contribution in contributions {
        hasher.update(&(contribution.worker as u64).to_be_bytes());
        hasher.update(&contribution.digest);
    }
    *hasher.finalize().as_bytes()
}

fn signature_message(digest: &[u8; 32]) -> Vec<u8> {
    let mut message = Vec::with_capacity(SIGNATURE_DOMAIN.len() + digest.len());
    message.extend_from_slice(SIGNATURE_DOMAIN);
    message.extend_from_slice(digest);
    message
}

fn hash_parts(domain: &str, parts: &[&[u8]]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(domain);
    for part in parts {
        hasher.update(&(part.len() as u64).to_be_bytes());
        hasher.update(part);
    }
    *hasher.finalize().as_bytes()
}

fn take<const N: usize>(bytes: &[u8], offset: &mut usize) -> Result<[u8; N]> {
    let end = offset
        .checked_add(N)
        .ok_or(DistributedProverError::MalformedContribution)?;
    let value = bytes
        .get(*offset..end)
        .ok_or(DistributedProverError::MalformedContribution)?
        .try_into()
        .map_err(|_| DistributedProverError::MalformedContribution)?;
    *offset = end;
    Ok(value)
}

fn take_request<const N: usize>(bytes: &[u8], offset: &mut usize) -> Result<[u8; N]> {
    let end = offset
        .checked_add(N)
        .ok_or(DistributedProverError::MalformedRequest)?;
    let value = bytes
        .get(*offset..end)
        .ok_or(DistributedProverError::MalformedRequest)?
        .try_into()
        .map_err(|_| DistributedProverError::MalformedRequest)?;
    *offset = end;
    Ok(value)
}
