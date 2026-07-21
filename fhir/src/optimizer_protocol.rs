//! Fail-closed transport for untrusted external optimizer workers.
//!
//! The worker may solve a problem and return certificate bytes, but neither its
//! identity nor its response envelope is verification authority.  A relying
//! party constructs an [`OptimizerJobRequest`] from a canonical problem, pins a
//! canonical solver manifest, and accepts a response only through
//! [`verify_optimizer_worker_result`].  That boundary binds the exact request,
//! session, nonce, solver identity, certificate format and certificate bytes;
//! it then delegates the bytes to an independent certificate checker before
//! consuming the request's replay identity.
//!
//! [`verify_qp_optimizer_worker_result`] is the typed fhIR QP adapter.  It
//! recomputes the exact `(P,q,A,l,u)` digest from the independently compiled
//! program and delegates the opaque `FHQPB001` bytes to
//! [`crate::verify_certified_qp`].

use crate::{
    canonical_qp_program_digest, verify_certified_qp, Compiled, ExactQpCertificateBundleError,
    VerifiedExactQpCertificate,
};
use sha2::{Digest, Sha256};
use std::collections::HashSet;

const REQUEST_MAGIC: &[u8; 8] = b"FHIROQ01";
const RESULT_MAGIC: &[u8; 8] = b"FHIROS01";
const REQUEST_DIGEST_DOMAIN: &[u8] = b"fhir/optimizer-request/v1";
const RESULT_CHECKSUM_DOMAIN: &[u8] = b"fhir/optimizer-result/v1";
const SOLVER_IDENTITY_DOMAIN: &[u8] = b"fhir/optimizer-solver-identity/v1";
const GENERIC_PROBLEM_DOMAIN: &[u8] = b"fhir/optimizer-canonical-problem/v1";
const CERTIFICATE_DIGEST_DOMAIN: &[u8] = b"fhir/optimizer-certificate/v1";
const REPLAY_ID_DOMAIN: &[u8] = b"fhir/optimizer-replay-id/v1";

pub const OPTIMIZER_PROTOCOL_VERSION: u16 = 1;
pub const FHQPB001_CERTIFICATE_VERSION: u16 = 1;
pub const MAX_SOLVER_MANIFEST_BYTES: usize = 1024 * 1024;
pub const MAX_CANONICAL_PROBLEM_BYTES: usize = 64 * 1024 * 1024;
pub const MAX_OPTIMIZER_CERTIFICATE_BYTES: usize = 64 * 1024 * 1024;

const REQUEST_WIRE_LEN: usize = 8 + 2 + 1 + 2 + 4 * 32;
const RESULT_FIXED_PREFIX_LEN: usize = 8 + 2 + 1 + 2 + 5 * 32 + 8 + 32;
const CHECKSUM_LEN: usize = 32;
pub const MAX_OPTIMIZER_RESULT_BYTES: usize =
    RESULT_FIXED_PREFIX_LEN + MAX_OPTIMIZER_CERTIFICATE_BYTES + CHECKSUM_LEN;

/// Certificate checker selected by the independently compiled fhIR program.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum OptimizerCertificateKind {
    CertF = 1,
    CertQp = 2,
}

impl OptimizerCertificateKind {
    fn from_wire(value: u8) -> Result<Self, OptimizerProtocolError> {
        match value {
            1 => Ok(Self::CertF),
            2 => Ok(Self::CertQp),
            found => Err(OptimizerProtocolError::UnknownCertificateKind { found }),
        }
    }
}

/// Domain-separated identity of the exact executable/version/config manifest
/// that the relying party is willing to dispatch to.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SolverIdentity([u8; 32]);

impl SolverIdentity {
    pub fn from_canonical_manifest(
        canonical_manifest: &[u8],
    ) -> Result<Self, OptimizerProtocolError> {
        if canonical_manifest.is_empty() {
            return Err(OptimizerProtocolError::EmptySolverManifest);
        }
        if canonical_manifest.len() > MAX_SOLVER_MANIFEST_BYTES {
            return Err(OptimizerProtocolError::SolverManifestTooLarge {
                actual: canonical_manifest.len(),
                maximum: MAX_SOLVER_MANIFEST_BYTES,
            });
        }
        let length = u64::try_from(canonical_manifest.len())
            .map_err(|_| OptimizerProtocolError::ArithmeticOverflow)?;
        let mut hasher = Sha256::new();
        hasher.update(SOLVER_IDENTITY_DOMAIN);
        hasher.update(length.to_be_bytes());
        hasher.update(canonical_manifest);
        Ok(Self(hasher.finalize().into()))
    }

    pub fn digest(self) -> [u8; 32] {
        self.0
    }
}

/// One canonical optimizer dispatch.  Session and nonce are mandatory and
/// independently bound: a response from an old session cannot be relabeled as
/// a fresh job, even when problem and solver are unchanged.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OptimizerJobRequest {
    certificate_kind: OptimizerCertificateKind,
    certificate_version: u16,
    problem_digest: [u8; 32],
    solver_identity: SolverIdentity,
    session_id: [u8; 32],
    nonce: [u8; 32],
}

impl OptimizerJobRequest {
    /// Construct a request from a complete canonical problem encoding.
    pub fn new(
        certificate_kind: OptimizerCertificateKind,
        certificate_version: u16,
        canonical_problem: &[u8],
        solver_identity: SolverIdentity,
        session_id: [u8; 32],
        nonce: [u8; 32],
    ) -> Result<Self, OptimizerProtocolError> {
        if canonical_problem.is_empty() {
            return Err(OptimizerProtocolError::EmptyCanonicalProblem);
        }
        if canonical_problem.len() > MAX_CANONICAL_PROBLEM_BYTES {
            return Err(OptimizerProtocolError::CanonicalProblemTooLarge {
                actual: canonical_problem.len(),
                maximum: MAX_CANONICAL_PROBLEM_BYTES,
            });
        }
        let length = u64::try_from(canonical_problem.len())
            .map_err(|_| OptimizerProtocolError::ArithmeticOverflow)?;
        let mut hasher = Sha256::new();
        hasher.update(GENERIC_PROBLEM_DOMAIN);
        hasher.update([certificate_kind as u8]);
        hasher.update(certificate_version.to_be_bytes());
        hasher.update(length.to_be_bytes());
        hasher.update(canonical_problem);
        Self::from_canonical_problem_digest(
            certificate_kind,
            certificate_version,
            hasher.finalize().into(),
            solver_identity,
            session_id,
            nonce,
        )
    }

    /// Construct a request from a digest produced by a format-specific
    /// canonicalizer.  Prefer [`Self::for_qp`] for fhIR QPs.
    pub fn from_canonical_problem_digest(
        certificate_kind: OptimizerCertificateKind,
        certificate_version: u16,
        problem_digest: [u8; 32],
        solver_identity: SolverIdentity,
        session_id: [u8; 32],
        nonce: [u8; 32],
    ) -> Result<Self, OptimizerProtocolError> {
        if certificate_version == 0 {
            return Err(OptimizerProtocolError::ZeroCertificateVersion);
        }
        if session_id == [0; 32] {
            return Err(OptimizerProtocolError::ZeroSessionId);
        }
        if nonce == [0; 32] {
            return Err(OptimizerProtocolError::ZeroNonce);
        }
        Ok(Self {
            certificate_kind,
            certificate_version,
            problem_digest,
            solver_identity,
            session_id,
            nonce,
        })
    }

    /// Construct an `FHQPB001` job by exact-lifting the complete public
    /// `(P,q,A,l,u)` image of an independently compiled fhIR QP.
    pub fn for_qp(
        compiled: &Compiled,
        solver_identity: SolverIdentity,
        session_id: [u8; 32],
        nonce: [u8; 32],
    ) -> Result<Self, OptimizerProtocolError> {
        let problem_digest = canonical_qp_program_digest(compiled)?;
        Self::from_canonical_problem_digest(
            OptimizerCertificateKind::CertQp,
            FHQPB001_CERTIFICATE_VERSION,
            problem_digest,
            solver_identity,
            session_id,
            nonce,
        )
    }

    pub fn certificate_kind(&self) -> OptimizerCertificateKind {
        self.certificate_kind
    }

    pub fn certificate_version(&self) -> u16 {
        self.certificate_version
    }

    pub fn problem_digest(&self) -> [u8; 32] {
        self.problem_digest
    }

    pub fn solver_identity(&self) -> SolverIdentity {
        self.solver_identity
    }

    pub fn session_id(&self) -> [u8; 32] {
        self.session_id
    }

    pub fn nonce(&self) -> [u8; 32] {
        self.nonce
    }

    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(REQUEST_WIRE_LEN);
        out.extend_from_slice(REQUEST_MAGIC);
        out.extend_from_slice(&OPTIMIZER_PROTOCOL_VERSION.to_be_bytes());
        out.push(self.certificate_kind as u8);
        out.extend_from_slice(&self.certificate_version.to_be_bytes());
        out.extend_from_slice(&self.problem_digest);
        out.extend_from_slice(&self.solver_identity.0);
        out.extend_from_slice(&self.session_id);
        out.extend_from_slice(&self.nonce);
        debug_assert_eq!(out.len(), REQUEST_WIRE_LEN);
        out
    }

    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, OptimizerProtocolError> {
        if bytes.len() != REQUEST_WIRE_LEN {
            return Err(OptimizerProtocolError::MalformedWire);
        }
        let mut cursor = Cursor::new(bytes);
        if cursor.take::<8>()? != *REQUEST_MAGIC {
            return Err(OptimizerProtocolError::MalformedWire);
        }
        let protocol_version = u16::from_be_bytes(cursor.take::<2>()?);
        if protocol_version != OPTIMIZER_PROTOCOL_VERSION {
            return Err(OptimizerProtocolError::UnsupportedProtocolVersion {
                found: protocol_version,
            });
        }
        let certificate_kind = OptimizerCertificateKind::from_wire(cursor.take::<1>()?[0])?;
        let certificate_version = u16::from_be_bytes(cursor.take::<2>()?);
        let problem_digest = cursor.take::<32>()?;
        let solver_identity = SolverIdentity(cursor.take::<32>()?);
        let session_id = cursor.take::<32>()?;
        let nonce = cursor.take::<32>()?;
        if !cursor.is_finished() {
            return Err(OptimizerProtocolError::MalformedWire);
        }
        let request = Self::from_canonical_problem_digest(
            certificate_kind,
            certificate_version,
            problem_digest,
            solver_identity,
            session_id,
            nonce,
        )?;
        if request.to_wire_bytes() != bytes {
            return Err(OptimizerProtocolError::MalformedWire);
        }
        Ok(request)
    }

    pub fn request_digest(&self) -> [u8; 32] {
        hash_parts(REQUEST_DIGEST_DOMAIN, &[&self.to_wire_bytes()])
    }

    pub fn replay_id(&self) -> [u8; 32] {
        hash_parts(
            REPLAY_ID_DOMAIN,
            &[&self.request_digest(), &self.session_id, &self.nonce],
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OptimizerProtocolError {
    ArithmeticOverflow,
    EmptySolverManifest,
    SolverManifestTooLarge {
        actual: usize,
        maximum: usize,
    },
    EmptyCanonicalProblem,
    CanonicalProblemTooLarge {
        actual: usize,
        maximum: usize,
    },
    ZeroCertificateVersion,
    ZeroSessionId,
    ZeroNonce,
    EmptyCertificate,
    CertificateTooLarge {
        actual: usize,
        maximum: usize,
    },
    WireTooLarge {
        actual: usize,
        maximum: usize,
    },
    MalformedWire,
    UnsupportedProtocolVersion {
        found: u16,
    },
    UnknownCertificateKind {
        found: u8,
    },
    ChecksumMismatch,
    CertificateDigestMismatch,
    RequestDigestMismatch,
    WrongCertificateKind {
        expected: OptimizerCertificateKind,
        found: OptimizerCertificateKind,
    },
    WrongCertificateVersion {
        expected: u16,
        found: u16,
    },
    WrongProblem,
    WrongSolver,
    StaleSession,
    WrongNonce,
    Replay,
    CertificateRejected {
        reason: String,
    },
    Qp(ExactQpCertificateBundleError),
}

impl std::fmt::Display for OptimizerProtocolError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for OptimizerProtocolError {}

impl From<ExactQpCertificateBundleError> for OptimizerProtocolError {
    fn from(value: ExactQpCertificateBundleError) -> Self {
        Self::Qp(value)
    }
}

/// Worker-side encoding.  This only packages a claim; it does not certify the
/// certificate or bless the solver.  Authority is minted exclusively by a
/// relying-party checker through [`verify_optimizer_worker_result`].
pub fn encode_optimizer_worker_result(
    request: &OptimizerJobRequest,
    certificate_bytes: &[u8],
) -> Result<Vec<u8>, OptimizerProtocolError> {
    if certificate_bytes.is_empty() {
        return Err(OptimizerProtocolError::EmptyCertificate);
    }
    if certificate_bytes.len() > MAX_OPTIMIZER_CERTIFICATE_BYTES {
        return Err(OptimizerProtocolError::CertificateTooLarge {
            actual: certificate_bytes.len(),
            maximum: MAX_OPTIMIZER_CERTIFICATE_BYTES,
        });
    }
    let certificate_len = u64::try_from(certificate_bytes.len())
        .map_err(|_| OptimizerProtocolError::ArithmeticOverflow)?;
    let certificate_digest = certificate_digest(
        request.certificate_kind,
        request.certificate_version,
        certificate_bytes,
    );
    let mut out =
        Vec::with_capacity(RESULT_FIXED_PREFIX_LEN + certificate_bytes.len() + CHECKSUM_LEN);
    out.extend_from_slice(RESULT_MAGIC);
    out.extend_from_slice(&OPTIMIZER_PROTOCOL_VERSION.to_be_bytes());
    out.push(request.certificate_kind as u8);
    out.extend_from_slice(&request.certificate_version.to_be_bytes());
    out.extend_from_slice(&request.request_digest());
    out.extend_from_slice(&request.problem_digest);
    out.extend_from_slice(&request.solver_identity.0);
    out.extend_from_slice(&request.session_id);
    out.extend_from_slice(&request.nonce);
    out.extend_from_slice(&certificate_len.to_be_bytes());
    out.extend_from_slice(&certificate_digest);
    out.extend_from_slice(certificate_bytes);
    let checksum = result_checksum(&out);
    out.extend_from_slice(&checksum);
    Ok(out)
}

/// Mutable replay state used at the final authorization boundary.
pub trait OptimizerReplayGuard {
    fn has_seen(&self, replay_id: &[u8; 32]) -> bool;

    /// Return `true` only when this call records the identifier for the first
    /// time.  Implementations shared across processes must make this operation
    /// atomic in their backing store.
    fn check_and_record(&mut self, replay_id: [u8; 32]) -> bool;
}

#[derive(Clone, Debug, Default)]
pub struct InMemoryOptimizerReplayGuard {
    seen: HashSet<[u8; 32]>,
}

impl InMemoryOptimizerReplayGuard {
    pub fn len(&self) -> usize {
        self.seen.len()
    }

    pub fn is_empty(&self) -> bool {
        self.seen.is_empty()
    }
}

impl OptimizerReplayGuard for InMemoryOptimizerReplayGuard {
    fn has_seen(&self, replay_id: &[u8; 32]) -> bool {
        self.seen.contains(replay_id)
    }

    fn check_and_record(&mut self, replay_id: [u8; 32]) -> bool {
        self.seen.insert(replay_id)
    }
}

/// Capability returned only after exact envelope binding, replay refusal, and
/// the caller-selected independent certificate checker all succeed.
#[derive(Clone, Debug)]
pub struct VerifiedOptimizerResult<T> {
    checked: T,
    request_digest: [u8; 32],
    problem_digest: [u8; 32],
    solver_identity: SolverIdentity,
    session_id: [u8; 32],
    nonce: [u8; 32],
    certificate_version: u16,
    certificate_digest: [u8; 32],
    certificate_bytes: Vec<u8>,
}

impl<T> VerifiedOptimizerResult<T> {
    pub fn checked(&self) -> &T {
        &self.checked
    }

    pub fn into_checked(self) -> T {
        self.checked
    }

    pub fn request_digest(&self) -> [u8; 32] {
        self.request_digest
    }

    pub fn problem_digest(&self) -> [u8; 32] {
        self.problem_digest
    }

    pub fn solver_identity(&self) -> SolverIdentity {
        self.solver_identity
    }

    pub fn session_id(&self) -> [u8; 32] {
        self.session_id
    }

    pub fn nonce(&self) -> [u8; 32] {
        self.nonce
    }

    pub fn certificate_version(&self) -> u16 {
        self.certificate_version
    }

    pub fn certificate_digest(&self) -> [u8; 32] {
        self.certificate_digest
    }

    pub fn certificate_bytes(&self) -> &[u8] {
        &self.certificate_bytes
    }
}

/// Verify one hostile worker response.  Envelope failures and replays are
/// refused before the certificate checker is invoked.  A rejected certificate
/// does not consume the replay identity, allowing a corrected response to the
/// same outstanding request.
pub fn verify_optimizer_worker_result<T, R, F, E>(
    expected: &OptimizerJobRequest,
    wire: &[u8],
    replay_guard: &mut R,
    checker: F,
) -> Result<VerifiedOptimizerResult<T>, OptimizerProtocolError>
where
    R: OptimizerReplayGuard,
    F: FnOnce(&[u8]) -> Result<T, E>,
    E: std::fmt::Display,
{
    let decoded = DecodedOptimizerResult::from_wire_bytes(wire)?;
    if decoded.request.certificate_kind != expected.certificate_kind {
        return Err(OptimizerProtocolError::WrongCertificateKind {
            expected: expected.certificate_kind,
            found: decoded.request.certificate_kind,
        });
    }
    if decoded.request.certificate_version != expected.certificate_version {
        return Err(OptimizerProtocolError::WrongCertificateVersion {
            expected: expected.certificate_version,
            found: decoded.request.certificate_version,
        });
    }
    if decoded.request.problem_digest != expected.problem_digest {
        return Err(OptimizerProtocolError::WrongProblem);
    }
    if decoded.request.solver_identity != expected.solver_identity {
        return Err(OptimizerProtocolError::WrongSolver);
    }
    if decoded.request.session_id != expected.session_id {
        return Err(OptimizerProtocolError::StaleSession);
    }
    if decoded.request.nonce != expected.nonce {
        return Err(OptimizerProtocolError::WrongNonce);
    }
    if decoded.request_digest != expected.request_digest() {
        return Err(OptimizerProtocolError::RequestDigestMismatch);
    }

    let replay_id = expected.replay_id();
    if replay_guard.has_seen(&replay_id) {
        return Err(OptimizerProtocolError::Replay);
    }
    let checked = checker(&decoded.certificate_bytes).map_err(|error| {
        OptimizerProtocolError::CertificateRejected {
            reason: error.to_string(),
        }
    })?;
    if !replay_guard.check_and_record(replay_id) {
        return Err(OptimizerProtocolError::Replay);
    }

    Ok(VerifiedOptimizerResult {
        checked,
        request_digest: decoded.request_digest,
        problem_digest: decoded.request.problem_digest,
        solver_identity: decoded.request.solver_identity,
        session_id: decoded.request.session_id,
        nonce: decoded.request.nonce,
        certificate_version: decoded.request.certificate_version,
        certificate_digest: decoded.certificate_digest,
        certificate_bytes: decoded.certificate_bytes,
    })
}

/// Typed `FHQPB001` relying-party boundary.  The QP program digest is
/// recomputed independently before any worker-controlled bytes reach the exact
/// PSD/KKT/problem-binding checker.
pub fn verify_qp_optimizer_worker_result<R: OptimizerReplayGuard>(
    compiled: &Compiled,
    expected: &OptimizerJobRequest,
    wire: &[u8],
    replay_guard: &mut R,
) -> Result<VerifiedOptimizerResult<VerifiedExactQpCertificate>, OptimizerProtocolError> {
    if expected.certificate_kind != OptimizerCertificateKind::CertQp {
        return Err(OptimizerProtocolError::WrongCertificateKind {
            expected: OptimizerCertificateKind::CertQp,
            found: expected.certificate_kind,
        });
    }
    if expected.certificate_version != FHQPB001_CERTIFICATE_VERSION {
        return Err(OptimizerProtocolError::WrongCertificateVersion {
            expected: FHQPB001_CERTIFICATE_VERSION,
            found: expected.certificate_version,
        });
    }
    if canonical_qp_program_digest(compiled)? != expected.problem_digest {
        return Err(OptimizerProtocolError::WrongProblem);
    }
    verify_optimizer_worker_result(expected, wire, replay_guard, |certificate_bytes| {
        verify_certified_qp(compiled, certificate_bytes)
    })
}

#[derive(Clone, Debug)]
struct DecodedOptimizerResult {
    request: OptimizerJobRequest,
    request_digest: [u8; 32],
    certificate_digest: [u8; 32],
    certificate_bytes: Vec<u8>,
}

impl DecodedOptimizerResult {
    fn from_wire_bytes(bytes: &[u8]) -> Result<Self, OptimizerProtocolError> {
        if bytes.len() > MAX_OPTIMIZER_RESULT_BYTES {
            return Err(OptimizerProtocolError::WireTooLarge {
                actual: bytes.len(),
                maximum: MAX_OPTIMIZER_RESULT_BYTES,
            });
        }
        if bytes.len() < RESULT_FIXED_PREFIX_LEN + 1 + CHECKSUM_LEN {
            return Err(OptimizerProtocolError::MalformedWire);
        }
        let payload_len = bytes
            .len()
            .checked_sub(CHECKSUM_LEN)
            .ok_or(OptimizerProtocolError::ArithmeticOverflow)?;
        if bytes[payload_len..] != result_checksum(&bytes[..payload_len]) {
            return Err(OptimizerProtocolError::ChecksumMismatch);
        }

        let mut cursor = Cursor::new(&bytes[..payload_len]);
        if cursor.take::<8>()? != *RESULT_MAGIC {
            return Err(OptimizerProtocolError::MalformedWire);
        }
        let protocol_version = u16::from_be_bytes(cursor.take::<2>()?);
        if protocol_version != OPTIMIZER_PROTOCOL_VERSION {
            return Err(OptimizerProtocolError::UnsupportedProtocolVersion {
                found: protocol_version,
            });
        }
        let certificate_kind = OptimizerCertificateKind::from_wire(cursor.take::<1>()?[0])?;
        let certificate_version = u16::from_be_bytes(cursor.take::<2>()?);
        let request_digest = cursor.take::<32>()?;
        let problem_digest = cursor.take::<32>()?;
        let solver_identity = SolverIdentity(cursor.take::<32>()?);
        let session_id = cursor.take::<32>()?;
        let nonce = cursor.take::<32>()?;
        let certificate_len_u64 = u64::from_be_bytes(cursor.take::<8>()?);
        let certificate_len = usize::try_from(certificate_len_u64)
            .map_err(|_| OptimizerProtocolError::ArithmeticOverflow)?;
        if certificate_len == 0 {
            return Err(OptimizerProtocolError::EmptyCertificate);
        }
        if certificate_len > MAX_OPTIMIZER_CERTIFICATE_BYTES {
            return Err(OptimizerProtocolError::CertificateTooLarge {
                actual: certificate_len,
                maximum: MAX_OPTIMIZER_CERTIFICATE_BYTES,
            });
        }
        let certificate_digest_from_wire = cursor.take::<32>()?;
        let expected_payload_len = RESULT_FIXED_PREFIX_LEN
            .checked_add(certificate_len)
            .ok_or(OptimizerProtocolError::ArithmeticOverflow)?;
        if expected_payload_len != payload_len {
            return Err(OptimizerProtocolError::MalformedWire);
        }
        let certificate_bytes = cursor.take_slice(certificate_len)?.to_vec();
        if !cursor.is_finished() {
            return Err(OptimizerProtocolError::MalformedWire);
        }

        let request = OptimizerJobRequest::from_canonical_problem_digest(
            certificate_kind,
            certificate_version,
            problem_digest,
            solver_identity,
            session_id,
            nonce,
        )?;
        if request.request_digest() != request_digest {
            return Err(OptimizerProtocolError::RequestDigestMismatch);
        }
        let computed_certificate_digest =
            certificate_digest(certificate_kind, certificate_version, &certificate_bytes);
        if computed_certificate_digest != certificate_digest_from_wire {
            return Err(OptimizerProtocolError::CertificateDigestMismatch);
        }
        Ok(Self {
            request,
            request_digest,
            certificate_digest: computed_certificate_digest,
            certificate_bytes,
        })
    }
}

fn certificate_digest(
    kind: OptimizerCertificateKind,
    certificate_version: u16,
    certificate_bytes: &[u8],
) -> [u8; 32] {
    hash_parts(
        CERTIFICATE_DIGEST_DOMAIN,
        &[
            &[kind as u8],
            &certificate_version.to_be_bytes(),
            &(certificate_bytes.len() as u64).to_be_bytes(),
            certificate_bytes,
        ],
    )
}

fn result_checksum(payload: &[u8]) -> [u8; 32] {
    hash_parts(RESULT_CHECKSUM_DOMAIN, &[payload])
}

fn hash_parts(domain: &[u8], parts: &[&[u8]]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    for part in parts {
        hasher.update(part);
    }
    hasher.finalize().into()
}

struct Cursor<'a> {
    bytes: &'a [u8],
    position: usize,
}

impl<'a> Cursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, position: 0 }
    }

    fn take<const N: usize>(&mut self) -> Result<[u8; N], OptimizerProtocolError> {
        let slice = self.take_slice(N)?;
        slice
            .try_into()
            .map_err(|_| OptimizerProtocolError::MalformedWire)
    }

    fn take_slice(&mut self, length: usize) -> Result<&'a [u8], OptimizerProtocolError> {
        let end = self
            .position
            .checked_add(length)
            .ok_or(OptimizerProtocolError::ArithmeticOverflow)?;
        let slice = self
            .bytes
            .get(self.position..end)
            .ok_or(OptimizerProtocolError::MalformedWire)?;
        self.position = end;
        Ok(slice)
    }

    fn is_finished(&self) -> bool {
        self.position == self.bytes.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{compile, products, run_certified_qp};
    use std::cell::Cell;

    fn solver(label: &[u8]) -> SolverIdentity {
        SolverIdentity::from_canonical_manifest(label).unwrap()
    }

    fn request() -> OptimizerJobRequest {
        OptimizerJobRequest::new(
            OptimizerCertificateKind::CertF,
            7,
            b"canonical cert-f integer system",
            solver(b"cert-f-worker/v7;flags=deterministic"),
            [0x31; 32],
            [0x52; 32],
        )
        .unwrap()
    }

    #[test]
    fn honest_result_mints_authority_once_and_replay_skips_checker() {
        let request = request();
        assert_eq!(
            OptimizerJobRequest::from_wire_bytes(&request.to_wire_bytes()).unwrap(),
            request
        );
        let response = encode_optimizer_worker_result(&request, b"exact cert-f bytes").unwrap();
        let calls = Cell::new(0usize);
        let mut replay = InMemoryOptimizerReplayGuard::default();
        let verified =
            verify_optimizer_worker_result(&request, &response, &mut replay, |certificate| {
                calls.set(calls.get() + 1);
                if certificate == b"exact cert-f bytes" {
                    Ok::<_, &'static str>("checked cert-f")
                } else {
                    Err("wrong certificate")
                }
            })
            .unwrap();
        assert_eq!(verified.checked(), &"checked cert-f");
        assert_eq!(verified.request_digest(), request.request_digest());
        assert_eq!(verified.problem_digest(), request.problem_digest());
        assert_eq!(verified.certificate_bytes(), b"exact cert-f bytes");
        assert_eq!(calls.get(), 1);
        assert_eq!(replay.len(), 1);

        let error = verify_optimizer_worker_result(&request, &response, &mut replay, |_| {
            calls.set(calls.get() + 1);
            Ok::<_, &'static str>(())
        })
        .unwrap_err();
        assert_eq!(error, OptimizerProtocolError::Replay);
        assert_eq!(calls.get(), 1, "replay must fail before checker");
    }

    #[test]
    fn rejected_certificate_does_not_burn_outstanding_request() {
        let request = request();
        let rejected = encode_optimizer_worker_result(&request, b"bad certificate").unwrap();
        let accepted = encode_optimizer_worker_result(&request, b"corrected certificate").unwrap();
        let mut replay = InMemoryOptimizerReplayGuard::default();
        let error = verify_optimizer_worker_result(&request, &rejected, &mut replay, |_| {
            Err::<(), _>("independent checker rejected it")
        })
        .unwrap_err();
        assert!(matches!(
            error,
            OptimizerProtocolError::CertificateRejected { .. }
        ));
        assert!(replay.is_empty());

        verify_optimizer_worker_result(&request, &accepted, &mut replay, |bytes| {
            if bytes == b"corrected certificate" {
                Ok::<_, &'static str>(())
            } else {
                Err("wrong bytes")
            }
        })
        .unwrap();
        assert_eq!(replay.len(), 1);
    }

    #[test]
    fn wrong_problem_solver_session_and_nonce_refuse_before_checker() {
        let source = request();
        let response = encode_optimizer_worker_result(&source, b"certificate").unwrap();
        let calls = Cell::new(0usize);

        let cases = [
            (
                OptimizerJobRequest::new(
                    OptimizerCertificateKind::CertF,
                    7,
                    b"different problem",
                    source.solver_identity(),
                    source.session_id(),
                    source.nonce(),
                )
                .unwrap(),
                OptimizerProtocolError::WrongProblem,
            ),
            (
                OptimizerJobRequest::new(
                    OptimizerCertificateKind::CertF,
                    7,
                    b"canonical cert-f integer system",
                    solver(b"other-worker/v7"),
                    source.session_id(),
                    source.nonce(),
                )
                .unwrap(),
                OptimizerProtocolError::WrongSolver,
            ),
            (
                OptimizerJobRequest::new(
                    OptimizerCertificateKind::CertF,
                    7,
                    b"canonical cert-f integer system",
                    source.solver_identity(),
                    [0x99; 32],
                    source.nonce(),
                )
                .unwrap(),
                OptimizerProtocolError::StaleSession,
            ),
            (
                OptimizerJobRequest::new(
                    OptimizerCertificateKind::CertF,
                    7,
                    b"canonical cert-f integer system",
                    source.solver_identity(),
                    source.session_id(),
                    [0x98; 32],
                )
                .unwrap(),
                OptimizerProtocolError::WrongNonce,
            ),
        ];

        for (expected, wanted) in cases {
            let mut replay = InMemoryOptimizerReplayGuard::default();
            let error = verify_optimizer_worker_result(&expected, &response, &mut replay, |_| {
                calls.set(calls.get() + 1);
                Ok::<_, &'static str>(())
            })
            .unwrap_err();
            assert_eq!(error, wanted);
            assert!(replay.is_empty());
        }
        assert_eq!(calls.get(), 0);
    }

    #[test]
    fn every_truncation_and_trailing_bytes_refuse_without_checker() {
        let request = request();
        let response = encode_optimizer_worker_result(&request, b"certificate").unwrap();
        let calls = Cell::new(0usize);
        for end in 0..response.len() {
            let mut replay = InMemoryOptimizerReplayGuard::default();
            assert!(verify_optimizer_worker_result(
                &request,
                &response[..end],
                &mut replay,
                |_| {
                    calls.set(calls.get() + 1);
                    Ok::<_, &'static str>(())
                },
            )
            .is_err());
            assert!(replay.is_empty());
        }
        let mut trailing = response;
        trailing.push(0);
        let mut replay = InMemoryOptimizerReplayGuard::default();
        assert!(
            verify_optimizer_worker_result(&request, &trailing, &mut replay, |_| {
                calls.set(calls.get() + 1);
                Ok::<_, &'static str>(())
            },)
            .is_err()
        );
        assert_eq!(calls.get(), 0);
    }

    #[test]
    fn digest_and_version_substitution_refuse() {
        let request = request();
        let mut substituted = encode_optimizer_worker_result(&request, b"certificate").unwrap();
        substituted[RESULT_FIXED_PREFIX_LEN] ^= 0x80;
        repair_result_checksum(&mut substituted);
        let mut replay = InMemoryOptimizerReplayGuard::default();
        let error = verify_optimizer_worker_result(&request, &substituted, &mut replay, |_| {
            Ok::<_, &'static str>(())
        })
        .unwrap_err();
        assert_eq!(error, OptimizerProtocolError::CertificateDigestMismatch);

        let wrong_version = OptimizerJobRequest::new(
            OptimizerCertificateKind::CertF,
            8,
            b"canonical cert-f integer system",
            request.solver_identity(),
            request.session_id(),
            request.nonce(),
        )
        .unwrap();
        let response = encode_optimizer_worker_result(&wrong_version, b"certificate").unwrap();
        let error = verify_optimizer_worker_result(&request, &response, &mut replay, |_| {
            Ok::<_, &'static str>(())
        })
        .unwrap_err();
        assert_eq!(
            error,
            OptimizerProtocolError::WrongCertificateVersion {
                expected: 7,
                found: 8,
            }
        );

        let mut wrong_protocol = encode_optimizer_worker_result(&request, b"certificate").unwrap();
        wrong_protocol[8..10].copy_from_slice(&2u16.to_be_bytes());
        repair_result_checksum(&mut wrong_protocol);
        let error = verify_optimizer_worker_result(&request, &wrong_protocol, &mut replay, |_| {
            Ok::<_, &'static str>(())
        })
        .unwrap_err();
        assert_eq!(
            error,
            OptimizerProtocolError::UnsupportedProtocolVersion { found: 2 }
        );
    }

    #[test]
    fn qp_adapter_binds_compiled_problem_and_exact_certificate() {
        let compiled = compile(&products::portfolio_qp_public()).unwrap();
        let request = OptimizerJobRequest::for_qp(
            &compiled,
            solver(b"qp-worker/osqp-0.6.3;fixed-lift=1e6"),
            [0x71; 32],
            [0x72; 32],
        )
        .unwrap();
        let certificate = run_certified_qp(&compiled)
            .unwrap()
            .to_wire_bytes()
            .unwrap();
        let response = encode_optimizer_worker_result(&request, &certificate).unwrap();
        let mut replay = InMemoryOptimizerReplayGuard::default();
        let verified =
            verify_qp_optimizer_worker_result(&compiled, &request, &response, &mut replay).unwrap();
        assert_eq!(verified.problem_digest(), request.problem_digest());
        assert_eq!(
            verified.checked().program_digest(),
            request.problem_digest()
        );

        let mut other_product = products::portfolio_qp_public();
        let crate::ast::ProductBody::Portfolio { lambda, .. } = &mut other_product.body else {
            unreachable!("portfolio fixture changed shape")
        };
        *lambda += 1.0;
        let wrong_compiled = compile(&other_product).unwrap();
        let mut fresh_replay = InMemoryOptimizerReplayGuard::default();
        let error = verify_qp_optimizer_worker_result(
            &wrong_compiled,
            &request,
            &response,
            &mut fresh_replay,
        )
        .unwrap_err();
        assert_eq!(error, OptimizerProtocolError::WrongProblem);
    }

    fn repair_result_checksum(wire: &mut [u8]) {
        let checksum_offset = wire.len() - CHECKSUM_LEN;
        let checksum = result_checksum(&wire[..checksum_offset]);
        wire[checksum_offset..].copy_from_slice(&checksum);
    }
}
